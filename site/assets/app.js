// Indicogni Core Runtime — Prove It: Formally Verified Software in Lean 4
// Strictly CSP-safe: zero eval, safe DOM textContent construction, zero external requests.

import { CHAPTER_INTERACTIVES } from "./chapter-data.js";

const STORAGE_KEY = "indicogni.proveit.v1";
const TOTAL_UNITS = 20; // 16 chapters + 4 checkpoints

function defaultState() {
  return {
    version: 1,
    theme: null,
    completed: {},
    predictions: {},
    labs: {},
    lastVisited: null
  };
}

export function loadProgress() {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY);
    if (!raw) return defaultState();
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== "object") return defaultState();
    return {
      version: 1,
      theme: parsed.theme === "dark" || parsed.theme === "light" ? parsed.theme : null,
      completed: parsed.completed && typeof parsed.completed === "object" ? parsed.completed : {},
      predictions: parsed.predictions && typeof parsed.predictions === "object" ? parsed.predictions : {},
      labs: parsed.labs && typeof parsed.labs === "object" ? parsed.labs : {},
      lastVisited: parsed.lastVisited && typeof parsed.lastVisited === "object" ? parsed.lastVisited : null
    };
  } catch (_) {
    return defaultState();
  }
}

export function saveProgress(state) {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify(state));
  } catch (_) {
    // Private browsing or quota limit: continue gracefully in memory.
  }
}

export function recordLabMilestone(labId) {
  const state = loadProgress();
  state.labs[labId] = true;
  saveProgress(state);
  refreshProgressBadges();
}

function getEffectiveTheme(state) {
  if (state.theme === "dark" || state.theme === "light") return state.theme;
  return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
}

function applyTheme(state) {
  const root = document.documentElement;
  if (state.theme === "dark" || state.theme === "light") {
    root.setAttribute("data-theme", state.theme);
  } else {
    root.removeAttribute("data-theme");
  }
  const effective = getEffectiveTheme(state);
  document.querySelectorAll("[data-action='toggle-theme']").forEach((btn) => {
    btn.textContent = effective === "dark" ? "Light theme (t)" : "Dark theme (t)";
    btn.setAttribute("aria-pressed", effective === "dark" ? "true" : "false");
  });
}

function toggleTheme() {
  const state = loadProgress();
  const current = getEffectiveTheme(state);
  state.theme = current === "dark" ? "light" : "dark";
  saveProgress(state);
  applyTheme(state);
}

export function refreshProgressBadges() {
  const state = loadProgress();
  const doneCount = Object.keys(state.completed).filter((k) => Boolean(state.completed[k])).length;
  const labCount = Object.keys(state.labs).filter((k) => Boolean(state.labs[k])).length;

  document.querySelectorAll("[data-progress-summary]").forEach((el) => {
    el.textContent = `${doneCount}/${TOTAL_UNITS} units · ${labCount}/6 labs`;
  });

  document.querySelectorAll("[data-unit-row]").forEach((row) => {
    const unitId = row.getAttribute("data-unit-row");
    const pill = row.querySelector("[data-unit-status]");
    if (!pill || !unitId) return;
    if (state.completed[unitId]) {
      pill.textContent = "Verified ✓";
      pill.classList.add("done");
    } else if (Object.prototype.hasOwnProperty.call(state.predictions, unitId)) {
      pill.textContent = "In progress";
      pill.classList.remove("done");
    } else {
      pill.textContent = "Unread";
      pill.classList.remove("done");
    }
  });
}

function initResumeBanner() {
  const banner = document.getElementById("resume-banner");
  if (!banner) return;
  const state = loadProgress();
  const doneCount = Object.keys(state.completed).filter((k) => Boolean(state.completed[k])).length;
  const labCount = Object.keys(state.labs).filter((k) => Boolean(state.labs[k])).length;
  const hasActivity = Boolean(state.lastVisited) || doneCount > 0 || labCount > 0;

  if (!hasActivity) {
    banner.hidden = true;
    return;
  }

  banner.hidden = false;
  const titleEl = document.getElementById("resume-title");
  const linkEl = document.getElementById("resume-link");
  if (titleEl && linkEl) {
    if (state.lastVisited && state.lastVisited.href && state.lastVisited.title) {
      titleEl.textContent = `${state.lastVisited.title} (${doneCount}/${TOTAL_UNITS} units verified, ${labCount}/6 labs explored)`;
      linkEl.setAttribute("href", state.lastVisited.href);
    } else {
      titleEl.textContent = `${doneCount}/${TOTAL_UNITS} units verified · ${labCount}/6 browser labs explored`;
      linkEl.setAttribute("href", "chapters/01.html");
    }
  }
}

function initProgressExportReset() {
  document.querySelectorAll("[data-action='export-progress']").forEach((btn) => {
    btn.addEventListener("click", () => {
      const state = loadProgress();
      const blob = new Blob([JSON.stringify(state, null, 2)], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "indicogni-proveit-progress.json";
      document.body.appendChild(a);
      a.click();
      a.remove();
      URL.revokeObjectURL(url);
    });
  });

  document.querySelectorAll("[data-action='reset-progress']").forEach((btn) => {
    let armed = false;
    btn.addEventListener("click", () => {
      if (!armed) {
        armed = true;
        btn.textContent = "Click again to confirm reset";
        window.setTimeout(() => {
          armed = false;
          btn.textContent = "Reset progress";
        }, 4000);
        return;
      }
      const currentTheme = loadProgress().theme;
      const fresh = defaultState();
      fresh.theme = currentTheme;
      saveProgress(fresh);
      armed = false;
      btn.textContent = "Progress cleared";
      refreshProgressBadges();
      initResumeBanner();
    });
  });
}

function trackChapterVisit() {
  const body = document.body;
  const unitId = body.getAttribute("data-unit-id");
  const unitTitle = body.getAttribute("data-unit-title");
  if (!unitId || !unitTitle) return;
  const state = loadProgress();
  state.lastVisited = {
    id: unitId,
    title: unitTitle,
    href: `chapters/${unitId}.html`
  };
  saveProgress(state);
}

function initPredictionCard() {
  const body = document.body;
  const unitId = body.getAttribute("data-unit-id");
  if (!unitId || !CHAPTER_INTERACTIVES[unitId]) return;

  const predConfig = CHAPTER_INTERACTIVES[unitId].prediction;
  const card = document.getElementById("prediction-card");
  if (!card || !predConfig) return;

  const optionsWrap = card.querySelector("[data-prediction-options]");
  const lockBtn = card.querySelector("[data-action='lock-prediction']");
  const statusBadge = card.querySelector("[data-prediction-status]");
  const revealBox = card.querySelector("[data-prediction-reveal]");
  const revealText = card.querySelector("[data-prediction-explanation]");

  if (!optionsWrap || !lockBtn || !revealBox || !revealText) return;

  let selectedIndex = null;
  const state = loadProgress();
  const lockedChoice = Object.prototype.hasOwnProperty.call(state.predictions, unitId)
    ? state.predictions[unitId]
    : null;

  const optionButtons = [];
  const letters = ["A", "B", "C", "D"];

  predConfig.options.forEach((optText, idx) => {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "prediction-option";

    const letterSpan = document.createElement("span");
    letterSpan.className = "option-letter";
    letterSpan.textContent = `${letters[idx] || String(idx + 1)}.`;

    const labelSpan = document.createElement("span");
    labelSpan.textContent = optText;

    btn.appendChild(letterSpan);
    btn.appendChild(labelSpan);

    btn.addEventListener("click", () => {
      if (Object.prototype.hasOwnProperty.call(loadProgress().predictions, unitId)) return;
      selectedIndex = idx;
      optionButtons.forEach((b, i) => {
        b.classList.toggle("is-selected", i === idx);
      });
      lockBtn.disabled = false;
    });

    optionButtons.push(btn);
    optionsWrap.appendChild(btn);
  });

  function renderLockedState(choiceIdx) {
    optionButtons.forEach((btn, idx) => {
      btn.disabled = true;
      btn.classList.remove("is-selected");
      if (idx === predConfig.answerIndex) {
        btn.classList.add("is-correct");
      } else if (idx === choiceIdx) {
        btn.classList.add("is-wrong");
      }
    });
    lockBtn.hidden = true;
    const matched = choiceIdx === predConfig.answerIndex;
    if (statusBadge) {
      statusBadge.textContent = matched
        ? `Prediction locked (${letters[choiceIdx]}) · Spot on`
        : `Prediction locked (${letters[choiceIdx]}) · Productive surprise`;
      statusBadge.className = matched ? "badge badge-verified" : "badge badge-open";
    }
    revealText.textContent = predConfig.explanation;
    revealBox.hidden = false;
  }

  if (lockedChoice !== null && typeof lockedChoice === "number") {
    renderLockedState(lockedChoice);
  } else {
    lockBtn.disabled = true;
    lockBtn.addEventListener("click", () => {
      if (selectedIndex === null) return;
      const latest = loadProgress();
      latest.predictions[unitId] = selectedIndex;
      saveProgress(latest);
      renderLockedState(selectedIndex);
      refreshProgressBadges();
    });
  }
}

let activeStepperControl = null;

function initWorkbenchStepper() {
  const body = document.body;
  const unitId = body.getAttribute("data-unit-id");
  if (!unitId || !CHAPTER_INTERACTIVES[unitId]) return;

  const wb = CHAPTER_INTERACTIVES[unitId].workbench;
  const root = document.getElementById("chapter-workbench");
  if (!root || !wb) return;

  const codeContainer = root.querySelector("[data-code-lines]");
  const counterEl = root.querySelector("[data-step-counter]");
  const statusBadge = root.querySelector("[data-goal-badge]");
  const objectsEl = root.querySelector("[data-infoview-objects]");
  const hypsEl = root.querySelector("[data-infoview-hyps]");
  const goalEl = root.querySelector("[data-infoview-goal]");
  const noteEl = root.querySelector("[data-infoview-note]");
  const playgroundLink = root.querySelector("[data-playground-link]");
  const copyCodeBtn = root.querySelector("[data-action='copy-lean']");

  if (!codeContainer || !objectsEl || !hypsEl || !goalEl || !noteEl) return;

  const lines = wb.code.split("\n");
  const lineStepMap = new Map();
  wb.steps.forEach((st, sIdx) => {
    if (typeof st.line === "number") {
      lineStepMap.set(st.line, sIdx);
    }
  });

  const lineEls = lines.map((lineText, idx) => {
    const lineNum = idx + 1;
    const row = document.createElement("div");
    row.className = "code-line";
    if (lineStepMap.has(lineNum)) {
      row.classList.add("is-steppable");
      row.setAttribute("title", "Click to inspect Lean Infoview at this line");
      row.addEventListener("click", () => {
        setStep(lineStepMap.get(lineNum));
      });
    }
    const no = document.createElement("span");
    no.className = "line-no";
    no.textContent = String(lineNum);
    const txt = document.createElement("span");
    txt.textContent = lineText.length > 0 ? lineText : " ";
    row.appendChild(no);
    row.appendChild(txt);
    codeContainer.appendChild(row);
    return row;
  });

  if (playgroundLink && wb.playgroundCode) {
    const encoded = encodeURIComponent(wb.playgroundCode);
    playgroundLink.setAttribute("href", `https://live.lean-lang.org/#code=${encoded}`);
  }

  if (copyCodeBtn && wb.playgroundCode) {
    copyCodeBtn.addEventListener("click", () => {
      copyTextWithFeedback(copyCodeBtn, wb.playgroundCode, "Copied Lean snippet");
    });
  }

  let currentStep = 0;

  function setStep(nextIdx) {
    const clamped = Math.max(0, Math.min(wb.steps.length - 1, nextIdx));
    currentStep = clamped;
    const st = wb.steps[currentStep];

    lineEls.forEach((el, idx) => {
      el.classList.toggle("is-active", idx + 1 === st.line);
    });

    if (counterEl) {
      counterEl.textContent = `Step ${currentStep + 1} / ${wb.steps.length}`;
    }

    objectsEl.textContent = st.objects || "(none)";
    hypsEl.textContent = st.hyps || "(none)";
    goalEl.textContent = st.goal;
    noteEl.textContent = st.note;

    goalEl.classList.remove("is-verified", "is-refuted");
    if (st.status === "verified") {
      goalEl.classList.add("is-verified");
      if (statusBadge) {
        statusBadge.textContent = "Goals accomplished";
        statusBadge.className = "badge badge-verified";
      }
    } else if (st.status === "refuted") {
      goalEl.classList.add("is-refuted");
      if (statusBadge) {
        statusBadge.textContent = "Counterexample / Stuck";
        statusBadge.className = "badge badge-refuted";
      }
    } else {
      if (statusBadge) {
        statusBadge.textContent = "Open Goal";
        statusBadge.className = "badge badge-open";
      }
    }
  }

  const prevBtn = root.querySelector("[data-action='step-prev']");
  const nextBtn = root.querySelector("[data-action='step-next']");
  const resetBtn = root.querySelector("[data-action='step-reset']");

  if (prevBtn) prevBtn.addEventListener("click", () => setStep(currentStep - 1));
  if (nextBtn) nextBtn.addEventListener("click", () => setStep(currentStep + 1));
  if (resetBtn) resetBtn.addEventListener("click", () => setStep(0));

  activeStepperControl = {
    next: () => setStep(currentStep + 1),
    prev: () => setStep(currentStep - 1)
  };

  setStep(0);
}

export function registerCustomStepper(control) {
  activeStepperControl = control;
}

export function copyTextWithFeedback(buttonEl, text, copiedLabel = "Copied!") {
  const original = buttonEl.getAttribute("data-orig-label") || buttonEl.textContent;
  buttonEl.setAttribute("data-orig-label", original);
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).then(() => {
      buttonEl.textContent = copiedLabel;
      window.setTimeout(() => {
        buttonEl.textContent = original;
      }, 1800);
    }).catch(() => {});
  }
}

function initCopyButtons() {
  document.querySelectorAll("[data-copy-text]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const text = btn.getAttribute("data-copy-text") || "";
      copyTextWithFeedback(btn, text, "Copied command ✓");
    });
  });
}

function initCompleteButton() {
  const unitId = document.body.getAttribute("data-unit-id");
  const btn = document.querySelector("[data-action='toggle-complete']");
  if (!unitId || !btn) return;

  function render() {
    const state = loadProgress();
    const isDone = Boolean(state.completed[unitId]);
    btn.classList.toggle("is-complete", isDone);
    btn.setAttribute("aria-pressed", isDone ? "true" : "false");
    btn.textContent = isDone ? "Chapter verified ✓ (click to unmark)" : "Mark chapter complete";
  }

  btn.addEventListener("click", () => {
    const state = loadProgress();
    if (state.completed[unitId]) {
      delete state.completed[unitId];
    } else {
      state.completed[unitId] = true;
    }
    saveProgress(state);
    render();
    refreshProgressBadges();
  });

  render();
}

function initShortcutModal() {
  const modal = document.getElementById("shortcut-modal");
  if (!modal) return;

  function openModal() {
    modal.hidden = false;
  }
  function closeModal() {
    modal.hidden = true;
  }
  function toggleModal() {
    modal.hidden = !modal.hidden;
  }

  document.querySelectorAll("[data-action='open-shortcuts']").forEach((btn) => {
    btn.addEventListener("click", toggleModal);
  });
  document.querySelectorAll("[data-action='close-shortcuts']").forEach((btn) => {
    btn.addEventListener("click", closeModal);
  });
  modal.addEventListener("click", (ev) => {
    if (ev.target === modal) closeModal();
  });

  document.addEventListener("keydown", (ev) => {
    const tag = ev.target && ev.target.tagName ? ev.target.tagName.toLowerCase() : "";
    const isInput = tag === "input" || tag === "textarea" || tag === "select" || (ev.target && ev.target.isContentEditable);

    if (ev.key === "Escape" && !modal.hidden) {
      closeModal();
      return;
    }
    if (isInput || ev.metaKey || ev.ctrlKey || ev.altKey) return;

    if (ev.key === "?") {
      ev.preventDefault();
      toggleModal();
    } else if (ev.key === "t") {
      ev.preventDefault();
      toggleTheme();
    } else if (ev.key === "j" && activeStepperControl) {
      ev.preventDefault();
      activeStepperControl.next();
    } else if (ev.key === "k" && activeStepperControl) {
      ev.preventDefault();
      activeStepperControl.prev();
    } else if (ev.key === "[") {
      const prevHref = document.body.getAttribute("data-prev-href");
      if (prevHref) window.location.href = prevHref;
    } else if (ev.key === "]") {
      const nextHref = document.body.getAttribute("data-next-href");
      if (nextHref) window.location.href = nextHref;
    }
  });
}

document.addEventListener("DOMContentLoaded", () => {
  const state = loadProgress();
  applyTheme(state);

  document.querySelectorAll("[data-action='toggle-theme']").forEach((btn) => {
    btn.addEventListener("click", toggleTheme);
  });

  trackChapterVisit();
  refreshProgressBadges();
  initResumeBanner();
  initProgressExportReset();
  initPredictionCard();
  initWorkbenchStepper();
  initCopyButtons();
  initCompleteButton();
  initShortcutModal();
});
