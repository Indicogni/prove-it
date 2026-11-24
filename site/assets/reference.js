// Indicogni Reference & Capstones Interactivity (Search, Category Filter, Copy)
// Strictly CSP-safe: zero eval, safe DOM manipulation only.

import { copyTextWithFeedback } from "./app.js";

function initLiveFilter() {
  const searchInput = document.querySelector("[data-filter-input]");
  const categoryBtns = document.querySelectorAll("[data-filter-cat]");
  const items = document.querySelectorAll("[data-filter-item]");
  const countEl = document.querySelector("[data-filter-count]");

  if (!searchInput && categoryBtns.length === 0) return;

  let activeCat = "all";

  function apply() {
    const query = searchInput ? searchInput.value.trim().toLowerCase() : "";
    let shown = 0;

    items.forEach((item) => {
      const cat = item.getAttribute("data-cat") || "all";
      const hay = (item.textContent || "").toLowerCase();
      const catOk = activeCat === "all" || cat === activeCat;
      const queryOk = query.length === 0 || hay.includes(query);
      const visible = catOk && queryOk;
      item.hidden = !visible;
      if (visible) shown += 1;
    });

    if (countEl) {
      countEl.textContent = `Showing ${shown} of ${items.length} entries`;
    }
  }

  if (searchInput) {
    searchInput.addEventListener("input", apply);
  }

  categoryBtns.forEach((btn) => {
    btn.addEventListener("click", () => {
      activeCat = btn.getAttribute("data-filter-cat") || "all";
      categoryBtns.forEach((b) => {
        b.classList.toggle("btn-primary", b === btn);
      });
      apply();
    });
  });

  apply();
}

function initCodeBlockCopy() {
  document.querySelectorAll("[data-copy-target]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const targetId = btn.getAttribute("data-copy-target");
      const targetEl = targetId ? document.getElementById(targetId) : null;
      if (!targetEl) return;
      copyTextWithFeedback(btn, targetEl.textContent || "", "Copied snippet ✓");
    });
  });
}

document.addEventListener("DOMContentLoaded", () => {
  initLiveFilter();
  initCodeBlockCopy();
});
