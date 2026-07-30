// ---------------------------------------------------------------
// RDP core (기존 코드로 가정하는 부분)
// ---------------------------------------------------------------

function perpendicularDistance(pt, lineStart, lineEnd) {
  const [x, y] = pt, [x1, y1] = lineStart, [x2, y2] = lineEnd;
  const dx = x2 - x1, dy = y2 - y1;
  if (dx === 0 && dy === 0) {
    return Math.hypot(x - x1, y - y1);
  }
  const t = ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy);
  const projX = x1 + t * dx, projY = y1 + t * dy;
  return Math.hypot(x - projX, y - projY);
}

function rdp(points, epsilon) {
  if (points.length < 3) return points;
  let maxDist = -1, index = 0;
  const first = points[0], last = points[points.length - 1];
  for (let i = 1; i < points.length - 1; i++) {
    const d = perpendicularDistance(points[i], first, last);
    if (d > maxDist) { maxDist = d; index = i; }
  }
  if (maxDist > epsilon) {
    const left = rdp(points.slice(0, index + 1), epsilon);
    const right = rdp(points.slice(index), epsilon);
    return left.slice(0, -1).concat(right);
  }
  return [first, last];
}

// ---------------------------------------------------------------
// 새로 추가하는 부분: rankPoints / simplifyToN
// ---------------------------------------------------------------

function rankPoints(points) {
  const scores = new Array(points.length).fill(-Infinity);
  scores[0] = Infinity;
  scores[points.length - 1] = Infinity;

  function recurse(start, end) {
    if (end <= start + 1) return;
    const first = points[start], last = points[end];
    let maxDist = -1, maxIdx = -1;
    for (let i = start + 1; i < end; i++) {
      const d = perpendicularDistance(points[i], first, last);
      if (d > maxDist) { maxDist = d; maxIdx = i; }
    }
    scores[maxIdx] = maxDist;
    recurse(start, maxIdx);
    recurse(maxIdx, end);
  }

  recurse(0, points.length - 1);
  return scores;
}

function simplifyToN(points, n) {
  if (n >= points.length) {
    return { points, epsilon: 0, epsilonRange: [0, 0] };
  }
  if (n < 2) {
    throw new Error("n은 최소 2 이상이어야 합니다.");
  }

  const scores = rankPoints(points);

  const indices = points.map((_, i) => i)
    .sort((a, b) => scores[b] - scores[a]);

  const keptIndices = indices.slice(0, n);
  const droppedIndices = indices.slice(n);

  const minKeptScore = Math.min(...keptIndices.map(i => scores[i]));
  const maxDroppedScore = droppedIndices.length > 0
    ? Math.max(...droppedIndices.map(i => scores[i]))
    : 0;

  const sortedKept = keptIndices.slice().sort((a, b) => a - b);

  return {
    points: sortedKept.map(i => points[i]),
    epsilon: minKeptScore,
    epsilonRange: [maxDroppedScore, minKeptScore]
  };
}

// simplifyToN을 확장: forcedIndices에 해당하는 점들은 점수와 무관하게 반드시 결과에 포함시킨다.
// (첫 점/마지막 점은 항상 포함되므로 forcedSet에 자동으로 추가된다.)
//
// 주의: 강제로 포함된 점의 원래 중요도(score)가 다른 "제외된" 점보다 낮을 수 있다.
// 이 경우 maxDroppedScore >= minKeptScore가 되어, 이 선택 결과를 그대로 재현하는
// 단일 epsilon 값이 존재하지 않는다 (validRange: false로 표시됨).
function simplifyToNForced(points, n, forcedIndices) {
  if (n < 2) {
    throw new Error("n은 최소 2 이상이어야 합니다.");
  }

  const scores = rankPoints(points);

  const forcedSet = new Set(forcedIndices);
  forcedSet.add(0);
  forcedSet.add(points.length - 1);

  // 정렬 우선순위: (1) 강제 포함 여부, (2) 원래 중요도(score)
  const order = points.map((_, i) => i).sort((a, b) => {
    const aForced = forcedSet.has(a) ? 1 : 0;
    const bForced = forcedSet.has(b) ? 1 : 0;
    if (aForced !== bForced) return bForced - aForced;
    return scores[b] - scores[a];
  });

  // n이 forcedSet 크기보다 작으면, 강제 포함을 지키기 위해 n을 자동으로 늘린다.
  const effectiveN = Math.max(n, forcedSet.size);
  const nWasAdjusted = effectiveN > n;

  const keptIndices = order.slice(0, effectiveN).sort((a, b) => a - b);
  const droppedIndices = order.slice(effectiveN);

  const minKeptScore = Math.min(...keptIndices.map(i => scores[i]));
  const maxDroppedScore = droppedIndices.length > 0
    ? Math.max(...droppedIndices.map(i => scores[i]))
    : 0;

  const validRange = maxDroppedScore < minKeptScore;

  return {
    points: keptIndices.map(i => points[i]),
    epsilon: minKeptScore,
    epsilonRange: [maxDroppedScore, minKeptScore],
    validRange,              // false면 단일 톨러런스로 재현 불가능한 조합
    effectiveN,              // 실제로 사용된 N (강제 포함 때문에 늘어났을 수 있음)
    nWasAdjusted,            // N이 자동으로 늘어났는지 여부
    forcedCount: forcedSet.size
  };
}

// ---------------------------------------------------------------
// 캔버스 드로잉 + UI 로직
// ---------------------------------------------------------------

const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');

let rawPoints = [];   // 현재 입력으로 쓰이는 점들 [[x,y], ...] (매번 단순화 결과로 교체됨)
let keptPoints = [];  // 마지막으로 계산된 단순화 결과 (미리보기용)
let isDrawing = false;
let endpointMarkers = { left: [], right: [], both: [] };

// history[i] = { points: [...], label: '...' } — 단순화를 실행하기 "직전" 상태의 스냅샷.
// 배열 끝(마지막 요소)이 가장 최근 이전 상태.
let history = [];

const statusEl = document.getElementById('status');
const resultEl = document.getElementById('result');
const nInput = document.getElementById('nInput');
const simplifyBtn = document.getElementById('simplifyBtn');
const undoBtn = document.getElementById('undoBtn');
const historyListEl = document.getElementById('historyList');
const coordReadoutEl = document.getElementById('coordReadout');
const baselineRange = document.getElementById('baselineRange');
const baselineValEl = document.getElementById('baselineVal');
const reboundThresholdEl = document.getElementById('reboundThreshold');
const copyJsonBtn = document.getElementById('copyJsonBtn');

// 기준선(y = 0)의 캔버스 픽셀 y좌표. 이보다 위는 논리 y가 양수, 아래는 음수.
let baselineY = parseInt(baselineRange.value, 10);

// 캔버스 픽셀 y좌표 → 기준선 기준 논리 y값 (위: +, 아래: -)
function toLogicalY(pixelY) {
  return baselineY - pixelY;
}
function toLogicalPoint(p) {
  return [p[0], toLogicalY(p[1])];
}

// "y값이 감소하다가 다시 증가로 반등하는 점"을 찾는다 (local minimum),
// 단 그 지점의 논리 y값이 threshold 이하일 때만 포함한다.
// points: [[x, pixelY], ...] 형태의 배열 (양 끝점은 이전/다음 이웃이 없으므로 제외)
function findReboundIndices(points, threshold) {
  const indices = [];
  for (let i = 1; i < points.length - 1; i++) {
    const yPrev = toLogicalY(points[i - 1][1]);
    const yCur = toLogicalY(points[i][1]);
    const yNext = toLogicalY(points[i + 1][1]);

    const isDecreasingThenIncreasing = (yPrev > yCur) && (yNext > yCur);
    if (isDecreasingThenIncreasing && yCur <= threshold) {
      indices.push(i);
    }
  }
  return indices;
}

function findIncreasingEndpoints(points, reboundIndices) {
  const leftSet = new Set();
  const rightSet = new Set();

  for (const center of reboundIndices) {
    let leftIdx = -1;
    for (let i = center - 1; i >= 0; i--) {
      const currentY = toLogicalY(points[i][1]);
      const towardCenterY = toLogicalY(points[i + 1][1]);
      if (currentY > towardCenterY) {
        leftIdx = i;
      } else {
        break;
      }
    }
    if (leftIdx >= 0) {
      leftSet.add(leftIdx);
    }

    let rightIdx = -1;
    for (let i = center + 1; i < points.length; i++) {
      const currentY = toLogicalY(points[i][1]);
      const towardCenterY = toLogicalY(points[i - 1][1]);
      if (currentY > towardCenterY) {
        rightIdx = i;
      } else {
        break;
      }
    }
    if (rightIdx >= 0) {
      rightSet.add(rightIdx);
    }
  }

  const both = [];
  const leftOnly = [];
  const rightOnly = [];

  for (const idx of leftSet) {
    if (rightSet.has(idx)) {
      both.push(idx);
    } else {
      leftOnly.push(idx);
    }
  }
  for (const idx of rightSet) {
    if (!leftSet.has(idx)) {
      rightOnly.push(idx);
    }
  }

  return {
    left: leftOnly,
    right: rightOnly,
    both
  };
}

function clearEndpointMarkers() {
  endpointMarkers = { left: [], right: [], both: [] };
}

function getPos(evt) {
  const rect = canvas.getBoundingClientRect();
  const cx = evt.touches ? evt.touches[0].clientX : evt.clientX;
  const cy = evt.touches ? evt.touches[0].clientY : evt.clientY;
  return [
    Math.round((cx - rect.left) * (canvas.width / rect.width)),
    Math.round((cy - rect.top) * (canvas.height / rect.height))
  ];
}

function startDraw(evt) {
  evt.preventDefault();
  isDrawing = true;
  rawPoints = [getPos(evt)];
  keptPoints = [];
  clearEndpointMarkers();
  history = [];
  renderHistory();
  resultEl.style.display = 'none';
  statusEl.textContent = '그리는 중...';
  redraw();
}

function moveDraw(evt) {
  if (!isDrawing) return;
  evt.preventDefault();
  const pos = getPos(evt);
  const last = rawPoints[rawPoints.length - 1];
  if (Math.hypot(pos[0] - last[0], pos[1] - last[1]) > 2) {
    rawPoints.push(pos);
    redraw();
  }
}

function endDraw(evt) {
  if (!isDrawing) return;
  isDrawing = false;
  if (rawPoints.length < 3) {
    statusEl.textContent = '점이 너무 적습니다. 더 길게 그려주세요.';
    return;
  }
  statusEl.textContent = `원본 점 ${rawPoints.length}개 · [단순화 실행] 버튼을 눌러주세요.`;
  updateNBounds();
  updateYRangeDisplay();
}

canvas.addEventListener('mousedown', startDraw);
canvas.addEventListener('mousemove', moveDraw);
canvas.addEventListener('mousemove', updateCoordReadout);
canvas.addEventListener('mouseleave', () => {
  coordReadoutEl.innerHTML = 'x: - · y: -';
});

function updateCoordReadout(evt) {
  const [px, py] = getPos(evt);
  const ly = toLogicalY(py);
  coordReadoutEl.innerHTML =
    `x: <span class="cx">${px}</span> · y: <span class="cy">${ly}</span>`;
}
window.addEventListener('mouseup', endDraw);
canvas.addEventListener('touchstart', startDraw, { passive: false });
canvas.addEventListener('touchmove', moveDraw, { passive: false });
canvas.addEventListener('touchend', endDraw);

function redraw() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);

  drawBaseline();

  // 원본 선
  if (rawPoints.length > 1) {
    ctx.beginPath();
    ctx.strokeStyle = getCss('--raw-line');
    ctx.lineWidth = 1.5;
    ctx.moveTo(rawPoints[0][0], rawPoints[0][1]);
    for (const p of rawPoints.slice(1)) ctx.lineTo(p[0], p[1]);
    ctx.stroke();
  }

  // 원본 점
  ctx.fillStyle = getCss('--raw-point');
  for (const p of rawPoints) {
    ctx.beginPath();
    ctx.arc(p[0], p[1], 2, 0, Math.PI * 2);
    ctx.fill();
  }

  // 단순화된 선/점
  if (keptPoints.length > 1) {
    ctx.beginPath();
    ctx.strokeStyle = getCss('--accent');
    ctx.lineWidth = 2.2;
    ctx.moveTo(keptPoints[0][0], keptPoints[0][1]);
    for (const p of keptPoints.slice(1)) ctx.lineTo(p[0], p[1]);
    ctx.stroke();
  }
  if (keptPoints.length > 0) {
    ctx.fillStyle = getCss('--kept-point');
    for (const p of keptPoints) {
      ctx.beginPath();
      ctx.arc(p[0], p[1], 5, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#0b0f14';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }
  }

  // 반등점(감소 → 증가 전환, y ≤ 임계값) 강조 표시
  const threshold = getReboundThreshold();
  const reboundIndices = findReboundIndices(rawPoints, threshold);
  if (reboundIndices.length > 0) {
    ctx.fillStyle = getCss('--rebound');
    for (const idx of reboundIndices) {
      const p = rawPoints[idx];
      ctx.beginPath();
      ctx.arc(p[0], p[1], 6, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#0b0f14';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }
  }

  if (endpointMarkers.left.length > 0) {
    ctx.fillStyle = getCss('--left-endpoint');
    for (const idx of endpointMarkers.left) {
      const p = rawPoints[idx];
      if (!p) continue;
      ctx.beginPath();
      ctx.arc(p[0], p[1], 6, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#0b0f14';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }
  }

  if (endpointMarkers.right.length > 0) {
    ctx.fillStyle = getCss('--right-endpoint');
    for (const idx of endpointMarkers.right) {
      const p = rawPoints[idx];
      if (!p) continue;
      ctx.beginPath();
      ctx.arc(p[0], p[1], 6, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#0b0f14';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }
  }

  if (endpointMarkers.both.length > 0) {
    ctx.fillStyle = getCss('--both-endpoint');
    for (const idx of endpointMarkers.both) {
      const p = rawPoints[idx];
      if (!p) continue;
      ctx.beginPath();
      ctx.arc(p[0], p[1], 6, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#0b0f14';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }
  }

  updateReboundCountDisplay(reboundIndices.length);
}

function getReboundThreshold() {
  const v = parseFloat(reboundThresholdEl.value);
  return Number.isFinite(v) ? v : 50;
}

function updateReboundCountDisplay(count) {
  const el = document.getElementById('reboundCountVal');
  if (!el) return;
  el.textContent = rawPoints.length === 0 ? '-' : `${count}개`;
}

function getCss(varName) {
  return getComputedStyle(document.documentElement).getPropertyValue(varName).trim();
}

function drawBaseline() {
  const w = canvas.width;

  // 기준선 (점선)
  ctx.save();
  ctx.setLineDash([6, 5]);
  ctx.strokeStyle = getCss('--baseline');
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  ctx.moveTo(0, baselineY);
  ctx.lineTo(w, baselineY);
  ctx.stroke();
  ctx.restore();

  // "y = 0" 라벨
  ctx.fillStyle = getCss('--baseline');
  ctx.font = '11px monospace';
  ctx.fillText('y = 0', 6, baselineY - 6);

  // 50px 간격 눈금 + 값 라벨 (양수: 위쪽, 음수: 아래쪽)
  ctx.strokeStyle = 'rgba(224, 79, 107, 0.35)';
  ctx.fillStyle = 'rgba(224, 79, 107, 0.75)';
  ctx.font = '10px monospace';
  const step = 50;
  for (let py = baselineY - step; py > 0; py -= step) {
    ctx.beginPath();
    ctx.moveTo(0, py);
    ctx.lineTo(8, py);
    ctx.stroke();
    ctx.fillText(`+${baselineY - py}`, 12, py + 3);
  }
  for (let py = baselineY + step; py < canvas.height; py += step) {
    ctx.beginPath();
    ctx.moveTo(0, py);
    ctx.lineTo(8, py);
    ctx.stroke();
    ctx.fillText(`${baselineY - py}`, 12, py + 3);
  }
}

function runSimplify() {
  if (rawPoints.length < 2) return;
  let n = parseInt(nInput.value, 10);
  if (!Number.isFinite(n) || n < 2) n = 2;
  if (n > rawPoints.length) n = rawPoints.length;
  nInput.value = n;

  if (n >= rawPoints.length) {
    statusEl.textContent = `N(${n})이 현재 점 개수(${rawPoints.length}) 이상이라 더 줄일 수 없습니다.`;
    return;
  }

  // 현재 화면에 표시 중인 반등점(빨간 점)을 강제 포함 대상으로 사용
  const threshold = getReboundThreshold();
  const forcedIndices = findReboundIndices(rawPoints, threshold);

  const { points, epsilon, epsilonRange, validRange, effectiveN, nWasAdjusted, forcedCount } =
    simplifyToNForced(rawPoints, n, forcedIndices);

  // 검증: epsilon을 "이번 단계의 원본"에 다시 넣었을 때 동일 개수가 나오는지 확인
  const verifyCount = rdp(rawPoints, epsilon).length;

  document.getElementById('rawCount').textContent = rawPoints.length;
  document.getElementById('keptCount').textContent = points.length;
  document.getElementById('epsilonVal').textContent = epsilon.toFixed(3);
  document.getElementById('epsilonRange').textContent =
    `(${epsilonRange[0].toFixed(3)}, ${epsilonRange[1].toFixed(3)}]`;

  if (!validRange) {
    document.getElementById('verifyVal').textContent =
      `재현 불가 — 강제 포함된 반등점의 중요도가 다른 제외된 점보다 낮아, 단일 톨러런스로는 동일한 결과가 나오지 않습니다.`;
  } else {
    document.getElementById('verifyVal').textContent =
      verifyCount === effectiveN
        ? `일치 (rdp 재실행 결과 ${verifyCount}개)`
        : `불일치 — rdp 재실행 결과 ${verifyCount}개 (epsilon 경계 근처 부동소수점 오차 가능)`;
  }

  const forcedInfoEl = document.getElementById('forcedInfoVal');
  if (forcedCount > 2) {
    forcedInfoEl.textContent = nWasAdjusted
      ? `반등점 ${forcedCount - 2}개 강제 포함 · N을 ${n} → ${effectiveN}로 자동 조정`
      : `반등점 ${forcedCount - 2}개 강제 포함 (N 조정 없음)`;
  } else {
    forcedInfoEl.textContent = '현재 강제 포함할 반등점 없음';
  }

  resultEl.style.display = 'block';

  // 현재 상태(이번 단계에 쓰인 입력)를 히스토리에 저장
  history.push({ points: rawPoints.map(p => p.slice()), label: `${rawPoints.length}개 → ${points.length}개` });

  // 결과를 새로운 입력값으로 교체 (동시에 orange 점으로 계속 강조 표시)
  rawPoints = points.map(p => p.slice());
  keptPoints = rawPoints.map(p => p.slice());
  clearEndpointMarkers();

  // N 입력값을 실제로 나온 결과 개수(effectiveN)에 맞춰 동기화
  nInput.value = effectiveN;

  updateNBounds();
  renderHistory();
  redraw();
  updateYRangeDisplay();
  statusEl.textContent = nWasAdjusted
    ? `단순화 완료 · 반등점 강제 포함으로 N이 ${n} → ${effectiveN}로 조정되었습니다.`
    : `단순화 완료 · 현재 ${rawPoints.length}개의 점이 새 입력이 되었습니다.`;
}

function undoOnce() {
  if (history.length === 0) return;
  const prev = history.pop();
  rawPoints = prev.points;
  keptPoints = [];
  clearEndpointMarkers();
  updateNBounds();
  renderHistory();
  redraw();
  updateYRangeDisplay();
  resultEl.style.display = 'none';
  statusEl.textContent = `되돌림 · 현재 ${rawPoints.length}개의 점.`;
}

function restoreHistoryIndex(idx) {
  // idx번째 스냅샷으로 점프하고, 그 이후의 히스토리는 모두 제거
  const target = history[idx];
  rawPoints = target.points;
  history = history.slice(0, idx);
  keptPoints = [];
  clearEndpointMarkers();
  updateNBounds();
  renderHistory();
  redraw();
  updateYRangeDisplay();
  resultEl.style.display = 'none';
  statusEl.textContent = `히스토리 복원 · 현재 ${rawPoints.length}개의 점.`;
}

function updateYRangeDisplay() {
  const el = document.getElementById('yRangeVal');
  if (!el) return;
  if (rawPoints.length === 0) {
    el.textContent = '-';
    return;
  }
  const logicalYs = rawPoints.map(p => toLogicalY(p[1]));
  const minY = Math.min(...logicalYs);
  const maxY = Math.max(...logicalYs);
  el.textContent = `${minY} ~ ${maxY}`;
}

function updateNBounds() {
  const maxN = Math.max(2, rawPoints.length - 1);
  nInput.max = maxN;
  if (parseInt(nInput.value, 10) > maxN) nInput.value = maxN;
  simplifyBtn.disabled = rawPoints.length < 3;
}

async function copyPointsAsJson() {
  if (rawPoints.length === 0) {
    statusEl.textContent = '복사할 점이 없습니다. 먼저 선을 그려주세요.';
    return;
  }

  const payload = rawPoints.map(([x, pixelY]) => ({
    x,
    y: toLogicalY(pixelY)
  }));
  const jsonText = JSON.stringify(payload, null, 2);

  try {
    await navigator.clipboard.writeText(jsonText);
    statusEl.textContent = `현재 점 ${payload.length}개를 JSON으로 클립보드에 복사했습니다.`;
    return;
  } catch (_) {
    // Clipboard API가 차단된 환경에서도 동작하도록 보조 경로를 사용한다.
  }

  const ta = document.createElement('textarea');
  ta.value = jsonText;
  ta.setAttribute('readonly', '');
  ta.style.position = 'fixed';
  ta.style.opacity = '0';
  ta.style.pointerEvents = 'none';
  document.body.appendChild(ta);
  ta.focus();
  ta.select();

  let copied = false;
  try {
    copied = document.execCommand('copy');
  } catch (_) {
    copied = false;
  }
  document.body.removeChild(ta);

  statusEl.textContent = copied
    ? `현재 점 ${payload.length}개를 JSON으로 클립보드에 복사했습니다.`
    : '클립보드 복사에 실패했습니다. 브라우저 권한을 확인해주세요.';
}

function renderHistory() {
  undoBtn.disabled = history.length === 0;

  if (history.length === 0) {
    historyListEl.innerHTML = '<div class="history-empty">아직 단순화 이력이 없습니다.</div>';
    return;
  }

  // 최근 것이 위로 오도록 역순 렌더링
  historyListEl.innerHTML = '';
  for (let i = history.length - 1; i >= 0; i--) {
    const item = history[i];
    const row = document.createElement('div');
    row.className = 'history-item';
    row.innerHTML = `
      <span class="h-label">단계 ${i + 1}</span>
      <span class="h-count">${item.label}</span>
      <button type="button" data-idx="${i}">이 시점으로</button>
    `;
    row.querySelector('button').addEventListener('click', () => restoreHistoryIndex(i));
    historyListEl.appendChild(row);
  }

  // 현재 상태 표시(가장 최근 결과)
  const currentRow = document.createElement('div');
  currentRow.className = 'history-item current';
  currentRow.innerHTML = `
    <span class="h-label">현재</span>
    <span class="h-count">${rawPoints.length}개</span>
    <span></span>
  `;
  historyListEl.prepend(currentRow);
}

simplifyBtn.addEventListener('click', runSimplify);
undoBtn.addEventListener('click', undoOnce);
copyJsonBtn.addEventListener('click', copyPointsAsJson);

baselineRange.addEventListener('input', () => {
  baselineY = parseInt(baselineRange.value, 10);
  baselineValEl.textContent = `${baselineY}px`;
  redraw();
  updateYRangeDisplay();
});

reboundThresholdEl.addEventListener('input', () => {
  clearEndpointMarkers();
  redraw();
});

document.getElementById('rescanBtn').addEventListener('click', () => {
  if (rawPoints.length === 0) {
    statusEl.textContent = '점이 없습니다. 먼저 선을 그려주세요.';
    return;
  }
  const threshold = getReboundThreshold();
  const found = findReboundIndices(rawPoints, threshold);
  clearEndpointMarkers();
  redraw(); // 내부에서 findReboundIndices를 다시 계산해 빨간 점으로 표시하고, 개수도 갱신함
  statusEl.textContent = `현재 ${rawPoints.length}개 점 중 반등점 ${found.length}개를 찾았습니다 (y ≤ ${threshold}).`;
});

document.getElementById('findEndpointsBtn').addEventListener('click', () => {
  if (rawPoints.length < 3) {
    statusEl.textContent = '점이 너무 적습니다. 먼저 선을 그려주세요.';
    return;
  }

  const threshold = getReboundThreshold();
  const reboundIndices = findReboundIndices(rawPoints, threshold);
  endpointMarkers = findIncreasingEndpoints(rawPoints, reboundIndices);
  redraw();

  const leftCount = endpointMarkers.left.length;
  const rightCount = endpointMarkers.right.length;
  const bothCount = endpointMarkers.both.length;
  statusEl.textContent = `끝점 탐색 완료 · 좌측 ${leftCount}개 · 우측 ${rightCount}개 · 겹침 ${bothCount}개`;
});

document.getElementById('clearBtn').addEventListener('click', () => {
  rawPoints = [];
  keptPoints = [];
  clearEndpointMarkers();
  history = [];
  simplifyBtn.disabled = true;
  resultEl.style.display = 'none';
  renderHistory();
  updateYRangeDisplay();
  statusEl.textContent = '선을 그려주세요.';
  redraw();
});

document.getElementById('nMinus').addEventListener('click', () => {
  nInput.value = Math.max(2, parseInt(nInput.value || 2, 10) - 1);
});
document.getElementById('nPlus').addEventListener('click', () => {
  nInput.value = parseInt(nInput.value || 2, 10) + 1;
});

simplifyBtn.disabled = true;
redraw();
