// Indicogni Interactive Browser Labs Engine (Labs 1–6)
// Zero external dependencies, zero eval, safe DOM construction, BigInt-exact 64-bit hardware math.

import { recordLabMilestone, registerCustomStepper, copyTextWithFeedback } from "./app.js";

function clearChildren(el) {
  while (el.firstChild) {
    el.removeChild(el.firstChild);
  }
}

function makeEl(tag, className, text) {
  const el = document.createElement(tag);
  if (className) el.className = className;
  if (typeof text === "string") el.textContent = text;
  return el;
}

/* ==========================================================================
   LAB 1: Interactive Lean Infoview & Tactic Stepper
   ========================================================================== */

const LAB1_THEOREMS = {
  quota: {
    title: "1. Safe Quota Withdraw Conservation",
    playground: `def withdraw (bal amt : Nat) : Option Nat :=
  if amt <= bal then some (bal - amt) else none

theorem withdraw_conserves (bal amt rem : Nat)
    (h : withdraw bal amt = some rem) :
    rem + amt = bal := by
  unfold withdraw at h
  split at h
  · simp only [Option.some.injEq] at h
    omega
  · contradiction`,
    steps: [
      {
        tactic: "(initial)",
        objects: "bal amt rem : Nat",
        hyps: "h : withdraw bal amt = some rem",
        goal: "⊢ rem + amt = bal",
        status: "open",
        expectedNext: "unfold",
        hint: "h mentions `withdraw`, which is currently opaque in the hypothesis. Unfold its definition at h first."
      },
      {
        tactic: "unfold withdraw at h",
        objects: "bal amt rem : Nat",
        hyps: "h : (if amt ≤ bal then some (bal - amt) else none) = some rem",
        goal: "⊢ rem + amt = bal",
        status: "open",
        expectedNext: "split",
        hint: "Now `h` contains an `if ... then ... else` expression. Case-split on the branch condition with `split at h`."
      },
      {
        tactic: "split at h",
        objects: "bal amt rem : Nat",
        hyps: "h_cond : amt ≤ bal\nh : some (bal - amt) = some rem\n(Branch 2 queued: ¬amt ≤ bal, h : none = some rem)",
        goal: "⊢ rem + amt = bal",
        status: "open",
        expectedNext: "simp only",
        hint: "Injectivity of `Option.some` turns `some (bal - amt) = some rem` into `bal - amt = rem` via `simp only`."
      },
      {
        tactic: "simp only [Option.some.injEq] at h",
        objects: "bal amt rem : Nat",
        hyps: "h_cond : amt ≤ bal\nh : bal - amt = rem",
        goal: "⊢ rem + amt = bal",
        status: "open",
        expectedNext: "omega",
        hint: "Notice `h_cond : amt ≤ bal` guards `Nat` subtraction so truncation cannot happen. Linear arithmetic (`omega`) closes this branch."
      },
      {
        tactic: "omega + contradiction",
        objects: "bal amt rem : Nat",
        hyps: "(Branch 1 closed by omega; Branch 2 `none = some rem` closed by contradiction)",
        goal: "Goals accomplished",
        status: "verified",
        expectedNext: null,
        hint: "Both branches are sealed in Lean's kernel. Without `amt ≤ bal`, `omega` would have refused the goal!"
      }
    ]
  },
  canary: {
    title: "2. Canary Router Fail-Closed on Unhealthy Target",
    playground: `inductive Route | stable | canary deriving DecidableEq

def chooseRoute (canaryHealthy : Bool) (bucket pct : Nat) : Route :=
  if canaryHealthy && bucket < pct then .canary else .stable

theorem unhealthy_forces_stable (bucket pct : Nat) :
    chooseRoute false bucket pct = .stable := by
  unfold chooseRoute
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]`,
    steps: [
      {
        tactic: "(initial)",
        objects: "bucket pct : Nat",
        hyps: "(none)",
        goal: "⊢ chooseRoute false bucket pct = Route.stable",
        status: "open",
        expectedNext: "unfold",
        hint: "Expose the implementation of `chooseRoute` in the goal using `unfold`."
      },
      {
        tactic: "unfold chooseRoute",
        objects: "bucket pct : Nat",
        hyps: "(none)",
        goal: "⊢ (if (false && bucket < pct) = true then Route.canary else Route.stable) = Route.stable",
        status: "open",
        expectedNext: "simp only",
        hint: "`false && anything` simplifies to `false`, collapsing the `if` expression via `simp only`."
      },
      {
        tactic: "simp only [Bool.false_and, ↓reduceIte]",
        objects: "bucket pct : Nat",
        hyps: "(none)",
        goal: "Goals accomplished",
        status: "verified",
        expectedNext: null,
        hint: "Verified across every possible `bucket` and `pct`—even `pct = 1000`."
      }
    ]
  },
  idempotent: {
    title: "3. Idempotent Write-Ahead Ledger Replay",
    playground: `structure Ledger where
  balance : Nat
  seenTx  : List Nat

def applyCredit (s : Ledger) (txId amt : Nat) : Ledger :=
  if txId ∈ s.seenTx then s
  else { balance := s.balance + amt, seenTx := txId :: s.seenTx }

theorem replay_idempotent (s : Ledger) (txId amt : Nat) :
    applyCredit (applyCredit s txId amt) txId amt = applyCredit s txId amt := by
  unfold applyCredit
  split <;> simp only [List.mem_cons, true_or, ↓reduceIte]`,
    steps: [
      {
        tactic: "(initial)",
        objects: "s : Ledger, txId amt : Nat",
        hyps: "(none)",
        goal: "⊢ applyCredit (applyCredit s txId amt) txId amt = applyCredit s txId amt",
        status: "open",
        expectedNext: "unfold",
        hint: "Unfold `applyCredit` so Lean sees the membership guard `txId ∈ s.seenTx`."
      },
      {
        tactic: "unfold applyCredit",
        objects: "s : Ledger, txId amt : Nat",
        hyps: "(none)",
        goal: "⊢ (let s1 := if txId ∈ s.seenTx then s else { balance := s.balance + amt, seenTx := txId :: s.seenTx }; if txId ∈ s1.seenTx then s1 else ...) = ...",
        status: "open",
        expectedNext: "split",
        hint: "Split on whether `txId` was already in `s.seenTx` before the first call."
      },
      {
        tactic: "split <;> simp only [List.mem_cons, true_or, ↓reduceIte]",
        objects: "s : Ledger, txId amt : Nat",
        hyps: "Case 1: txId ∈ s.seenTx (no-op twice)\nCase 2: txId ∉ s.seenTx (second call sees txId ∈ txId :: s.seenTx)",
        goal: "Goals accomplished",
        status: "verified",
        expectedNext: null,
        hint: "Crash recovery can replay `applyCredit` arbitrarily many times without double-crediting."
      }
    ]
  }
};

function initLab1() {
  const root = document.getElementById("lab1-root");
  if (!root) return;

  const selectEl = document.getElementById("lab1-select");
  const prevBtn = document.getElementById("lab1-prev");
  const nextBtn = document.getElementById("lab1-next");
  const resetBtn = document.getElementById("lab1-reset");
  const counterEl = document.getElementById("lab1-counter");
  const badgeEl = document.getElementById("lab1-badge");
  const objEl = document.getElementById("lab1-objects");
  const hypEl = document.getElementById("lab1-hyps");
  const goalEl = document.getElementById("lab1-goal");
  const feedbackEl = document.getElementById("lab1-feedback");
  const playLink = document.getElementById("lab1-playground");
  const paletteWrap = document.getElementById("lab1-palette");

  let currentKey = "quota";
  let stepIdx = 0;

  const TACTICS = ["unfold", "split", "simp only", "omega", "rfl"];

  function render() {
    const thm = LAB1_THEOREMS[currentKey];
    const st = thm.steps[stepIdx];
    counterEl.textContent = `Step ${stepIdx + 1} / ${thm.steps.length} · ${st.tactic}`;
    objEl.textContent = st.objects;
    hypEl.textContent = st.hyps;
    goalEl.textContent = st.goal;
    goalEl.classList.toggle("is-verified", st.status === "verified");
    badgeEl.textContent = st.status === "verified" ? "Goals accomplished" : "Open Goal";
    badgeEl.className = st.status === "verified" ? "badge badge-verified" : "badge badge-open";
    feedbackEl.textContent = st.hint;
    playLink.setAttribute("href", `https://live.lean-lang.org/#code=${encodeURIComponent(thm.playground)}`);

    if (st.status === "verified") {
      recordLabMilestone("lab1");
    }
  }

  TACTICS.forEach((tac) => {
    const btn = makeEl("button", "btn btn-sm", `Try: ${tac}`);
    btn.type = "button";
    btn.addEventListener("click", () => {
      const thm = LAB1_THEOREMS[currentKey];
      const st = thm.steps[stepIdx];
      if (!st.expectedNext) {
        feedbackEl.textContent = "No goals remain—this theorem is already complete!";
        return;
      }
      if (tac === st.expectedNext) {
        stepIdx = Math.min(thm.steps.length - 1, stepIdx + 1);
        render();
      } else {
        const reason = tac === "rfl"
          ? "`rfl` failed: both sides are not definitionally equal without case-splitting or arithmetic."
          : tac === "omega"
            ? "`omega` failed: goal still hides control flow (`if`/`match`) or function definitions."
            : `Tactic \`${tac}\` does not match the top-level connective here. Hint: ${st.hint}`;
        feedbackEl.textContent = reason;
      }
    });
    paletteWrap.appendChild(btn);
  });

  selectEl.addEventListener("change", () => {
    currentKey = selectEl.value;
    stepIdx = 0;
    render();
  });
  prevBtn.addEventListener("click", () => {
    stepIdx = Math.max(0, stepIdx - 1);
    render();
  });
  nextBtn.addEventListener("click", () => {
    const thm = LAB1_THEOREMS[currentKey];
    stepIdx = Math.min(thm.steps.length - 1, stepIdx + 1);
    render();
  });
  resetBtn.addEventListener("click", () => {
    stepIdx = 0;
    render();
  });

  registerCustomStepper({
    next: () => {
      const thm = LAB1_THEOREMS[currentKey];
      stepIdx = Math.min(thm.steps.length - 1, stepIdx + 1);
      render();
    },
    prev: () => {
      stepIdx = Math.max(0, stepIdx - 1);
      render();
    }
  });

  render();
}

/* ==========================================================================
   LAB 2: Fencing-Lease Split-Brain BFS Explorer vs Inductive Invariant Funnel
   ========================================================================== */

function runFencingBfs(allowDelay, enableFencing) {
  // State: { c1Lease, c2Lease, leaderEpoch, storageEpoch, storageVal, committedVal, delayedPacket }
  const init = {
    leaderEpoch: 1,
    storageEpoch: 1,
    storageVal: "init",
    committedEpoch2: false,
    stalePacketInFlight: false
  };

  const keyOf = (s) =>
    `${s.leaderEpoch}|${s.storageEpoch}|${s.storageVal}|${s.committedEpoch2 ? 1 : 0}|${s.stalePacketInFlight ? 1 : 0}`;

  const queue = [{ state: init, trace: ["Init: leaderEpoch=1, storage=(epoch=1, val='init')"] }];
  const visited = new Set([keyOf(init)]);
  let violationTrace = null;

  while (queue.length > 0) {
    const { state, trace } = queue.shift();

    // Safety property: once epoch-2 leader commits 'v2_clean', storageVal must never revert to 'v1_stale'.
    if (state.committedEpoch2 && state.storageVal === "v1_stale") {
      violationTrace = trace;
      break;
    }

    const transitions = [];

    // Action 1: Client 1 (epoch 1) prepares a write; if network/GC pause enabled, packet hangs in flight
    if (allowDelay && state.leaderEpoch === 1 && !state.stalePacketInFlight) {
      transitions.push({
        label: "Client1Pause: Client 1 (epoch 1) sends Write(epoch=1, 'v1_stale'), paused in network",
        next: { ...state, stalePacketInFlight: true }
      });
    }

    // Action 2: Lease expires; Coordinator grants epoch 2 to Client 2
    if (state.leaderEpoch === 1) {
      transitions.push({
        label: "GrantEpoch2: Lease timeout -> Client 2 elected with epoch=2",
        next: { ...state, leaderEpoch: 2 }
      });
    }

    // Action 3: Client 2 (epoch 2) writes 'v2_clean' to storage and confirms commit
    if (state.leaderEpoch === 2 && !state.committedEpoch2) {
      if (!enableFencing || 2 >= state.storageEpoch) {
        transitions.push({
          label: "Client2Commit: Storage accepts Write(epoch=2, 'v2_clean'); storageEpoch := 2",
          next: {
            ...state,
            storageEpoch: 2,
            storageVal: "v2_clean",
            committedEpoch2: true
          }
        });
      }
    }

    // Action 4: Delayed packet from Client 1 (epoch 1) arrives at Storage
    if (state.stalePacketInFlight) {
      if (!enableFencing || 1 >= state.storageEpoch) {
        transitions.push({
          label: "DeliverDelayedWrite(epoch=1): Storage ACCEPTS stale 'v1_stale' (no fencing check!)",
          next: {
            ...state,
            storageVal: "v1_stale",
            stalePacketInFlight: false
          }
        });
      } else {
        transitions.push({
          label: "DeliverDelayedWrite(epoch=1): Storage REJECTS 1 < storageEpoch(2) via Fencing Token!",
          next: {
            ...state,
            stalePacketInFlight: false
          }
        });
      }
    }

    for (const tr of transitions) {
      const k = keyOf(tr.next);
      if (!visited.has(k)) {
        visited.add(k);
        queue.push({ state: tr.next, trace: [...trace, tr.label] });
      }
    }
  }

  return {
    exploredCount: visited.size,
    violationTrace
  };
}

function initLab2() {
  const delayToggle = document.getElementById("lab2-delay");
  const fenceToggle = document.getElementById("lab2-fence");
  const gardenBtn = document.getElementById("lab2-garden-btn");
  const statusEl = document.getElementById("lab2-status");
  const traceList = document.getElementById("lab2-trace");
  const funnelNote = document.getElementById("lab2-funnel-note");
  if (!delayToggle || !fenceToggle || !traceList) return;

  function update() {
    recordLabMilestone("lab2");
    const allowDelay = delayToggle.checked;
    const enableFencing = fenceToggle.checked;
    const res = runFencingBfs(allowDelay, enableFencing);

    clearChildren(traceList);

    if (res.violationTrace) {
      statusEl.textContent = `SPLIT-BRAIN COUNTEREXAMPLE (${res.exploredCount} states searched)`;
      statusEl.className = "badge badge-refuted";
      res.violationTrace.forEach((line, idx) => {
        const li = makeEl(
          "li",
          idx === res.violationTrace.length - 1 ? "trace-step is-violation" : "trace-step",
          `${idx}. ${line}`
        );
        traceList.appendChild(li);
      });
      funnelNote.textContent =
        "Gear 1 caught a real bug in 4 steps! Do NOT attempt a Gear 2 Lean proof yet—fix the protocol by enabling the Monotonic Fencing Guard.";
    } else {
      statusEl.textContent = `BFS SAFE (${res.exploredCount} reachable states verified)`;
      statusEl.className = "badge badge-verified";
      const msg = enableFencing
        ? [
            "0. Init: leaderEpoch=1, storageEpoch=1",
            "1. Client1Pause: Write(epoch=1, 'v1_stale') delayed in network",
            "2. GrantEpoch2 + Client2Commit: storageEpoch := 2, val := 'v2_clean'",
            "3. DeliverDelayedWrite(epoch=1): REJECTED because 1 < storageEpoch(2) ✓",
            "Gear 1 exhausted bounded states; Gear 2 seals ALL unbounded epochs N ∈ Nat!"
          ]
        : [
            "0. Without network delay/GC pause, serial execution looks safe in unit tests.",
            "Toggle 'Simulate GC Pause / Delayed Packet' ON to see what unit tests miss!"
          ];
      msg.forEach((line) => {
        traceList.appendChild(makeEl("li", "trace-step", line));
      });
      funnelNote.textContent = enableFencing
        ? "With fencing active, the protocol is safe. Yet proving `Safe` directly by induction still fails on unreachable 'Garden-of-Eden' states unless strengthened with `committedEpoch2 → storageEpoch ≥ 2`."
        : "Happy-path tests only explore the non-delayed slice of state space.";
    }
  }

  delayToggle.addEventListener("change", update);
  fenceToggle.addEventListener("change", update);
  if (gardenBtn) {
    gardenBtn.addEventListener("click", () => {
      recordLabMilestone("lab2");
      funnelNote.textContent =
        "Garden-of-Eden Test: Pick arbitrary state s = { committedEpoch2 := true, storageEpoch := 0, storageVal := 'v2_clean', stalePacketInFlight := true }. Notice `Safe s` is TRUE right now! Yet one step (`DeliverDelayedWrite(epoch=1)`) passes `1 >= 0` and overwrites `'v2_clean'`! Strengthening the invariant with `committedEpoch2 → storageEpoch ≥ 2` carves out this unreachable state so Gear 2 induction succeeds.";
    });
  }

  update();
}

/* ==========================================================================
   LAB 3: Kernel Trust & #print axioms Taint DAG Inspector
   ========================================================================== */

function initLab3() {
  const root = document.getElementById("lab3-root");
  if (!root) return;

  const checks = {
    core: document.getElementById("lab3-core"),
    classical: document.getElementById("lab3-classical"),
    bv: document.getElementById("lab3-bv"),
    native: document.getElementById("lab3-native"),
    customAx: document.getElementById("lab3-axiom"),
    sorry: document.getElementById("lab3-sorry"),
    implBy: document.getElementById("lab3-implby")
  };

  const axiomsOut = document.getElementById("lab3-axioms-out");
  const tier0Badge = document.getElementById("lab3-tier0");
  const tier1Badge = document.getElementById("lab3-tier1");
  const explainOut = document.getElementById("lab3-explain");

  function render() {
    recordLabMilestone("lab3");
    const axList = ["propext", "Quot.sound"];
    if (checks.classical.checked) axList.push("Classical.choice");
    if (checks.bv.checked || checks.native.checked) {
      axList.push("Lean.ofReduceBool", "Lean.trustCompiler");
    }
    if (checks.customAx.checked) axList.push("my_unverified_assumption");
    if (checks.sorry.checked) axList.push("sorryAx");

    axiomsOut.textContent = `'withdraw_safe' depends on axioms: [${axList.join(", ")}]`;

    const hasSoundnessHole =
      checks.native.checked || checks.customAx.checked || checks.sorry.checked || checks.implBy.checked;

    // Tier 0 (--strict-kernel): allows only propext, Quot.sound, Classical.choice, zero implBy
    const tier0Pass = !hasSoundnessHole && !checks.bv.checked;
    // Tier 1 (--trust-tier=bv-lrat): allows bv_decide ONLY when zero raw native_decide & zero soundness holes
    const tier1Pass = !hasSoundnessHole;

    tier0Badge.textContent = tier0Pass ? "Tier 0 (--strict-kernel): PASS ✓" : "Tier 0 (--strict-kernel): REJECT ✗";
    tier0Badge.className = tier0Pass ? "badge badge-verified" : "badge badge-refuted";

    tier1Badge.textContent = tier1Pass ? "Tier 1 (--trust-tier=bv-lrat): PASS ✓" : "Tier 1 (--trust-tier=bv-lrat): REJECT ✗";
    tier1Badge.className = tier1Pass ? "badge badge-verified" : "badge badge-refuted";

    const notes = [];
    if (checks.implBy.checked) {
      notes.push(
        "CRITICAL TRAP: `@[implemented_by]` does NOT appear in `#print axioms`! The Lean kernel proved the pure model, while the compiler swapped in unverified runtime code. `lake exe verigate` scans environment attributes to block this."
      );
    }
    if (checks.native.checked && checks.bv.checked) {
      notes.push(
        "COLLISION ALERT: Both `bv_decide` and raw `native_decide` emit `Lean.ofReduceBool`. Tier 1 inspects syntax/elaboration trees to allow verified LRAT bit-blasting while unconditionally rejecting raw `native_decide`."
      );
    } else if (checks.native.checked) {
      notes.push(
        "`native_decide` trusts the entire C compiler and linked runtime inside your proof TCB—unconditionally rejected by `verigate`."
      );
    } else if (checks.bv.checked) {
      notes.push(
        "`bv_decide` checks an LRAT UNSAT certificate via compiled reflection (`Lean.ofReduceBool`). Rejected in strict Tier 0; permitted in explicit Tier 1 (`--trust-tier=bv-lrat`) for 64-bit hardware specs."
      );
    }
    if (checks.sorry.checked) {
      notes.push("`sorryAx` marks an unfinished proof hole—every theorem downstream is tainted.");
    }
    if (checks.customAx.checked) {
      notes.push("Custom `axiom` declarations let an AI assert `False` directly. `verigate` whitelists strictly standard axioms.");
    }
    if (notes.length === 0) {
      notes.push(
        "Pure Gold Standard: Only Lean's tiny kernel (`propext`, `Quot.sound`, and optional `Classical.choice`) sits inside your Trusted Computing Base."
      );
    }
    explainOut.textContent = notes.join(" ");
  }

  Object.values(checks).forEach((el) => {
    if (el) el.addEventListener("change", render);
  });
  render();
}

/* ==========================================================================
   LAB 4: Runtime Proof Erasure & Decidable Bridge Inspector
   ========================================================================== */

function initLab4() {
  const idxInput = document.getElementById("lab4-idx");
  const capInput = document.getElementById("lab4-cap");
  const roleSelect = document.getElementById("lab4-role");
  const elaboratedOut = document.getElementById("lab4-elaborated");
  const compiledOut = document.getElementById("lab4-compiled");
  const summaryBadge = document.getElementById("lab4-badge");
  if (!idxInput || !capInput || !elaboratedOut || !compiledOut) return;

  function render() {
    recordLabMilestone("lab4");
    const idx = Math.max(0, parseInt(idxInput.value || "0", 10) || 0);
    const cap = Math.max(1, parseInt(capInput.value || "16", 10) || 16);
    const role = roleSelect.value;
    const inBounds = idx < cap;
    const canDeploy = role === "Admin";

    if (inBounds) {
      summaryBadge.textContent = `Valid Subtype Witness (${idx} < ${cap}) · Proof Erased to 0 Bytes`;
      summaryBadge.className = "badge badge-verified";
      elaboratedOut.textContent =
        `-- Elaborated Lean 4 Kernel Term (Compile Time)\n` +
        `let slot : { i : UInt64 // i.toNat < ${cap} } :=\n` +
        `  ⟨${idx}, (h_bounds : ${idx} < ${cap})⟩\n` +
        `let auth : Decidable (Allows .${role} .Deploy) :=\n` +
        `  ${canDeploy ? "isTrue (h_rbac : Allows .Admin .Deploy)" : "isFalse (h_deny : ¬Allows ." + role + " .Deploy)"}\n` +
        `-- Array.uget ring slot.val slot.property (no redundant bounds check!)`;
      compiledOut.textContent =
        `// Lean LCNF / Emitted C Representation (Runtime)\n` +
        `uint64_t slot = ${idx}ULL; // proof field 'property : Prop' -> lcErased (0 bytes!)\n` +
        `uint8_t  auth = ${canDeploy ? "1" : "0"};    // Decidable bridges cleanly to 1-byte tag\n` +
        `lean_object* elem = lean_array_uget(ring, slot); // direct unguarded load!`;
    } else {
      summaryBadge.textContent = `Bounds Rejected at Boundary (${idx} ≥ ${cap}) · Safe None`;
      summaryBadge.className = "badge badge-open";
      elaboratedOut.textContent =
        `-- Dependent 'if h : ${idx} < ${cap}' takes the 'else' branch:\n` +
        `-- Proof witness h_not : ¬(${idx} < ${cap}) synthesized by Decidable (<)\n` +
        `-- Constructing ⟨${idx}, _⟩ : Fin ${cap} is a COMPILE-TIME TYPE ERROR.\n` +
        `Result: Option.none`;
      compiledOut.textContent =
        `// Boundary check runs ONCE when parsing untrusted input:\n` +
        `if (!(${idx}ULL < ${cap}ULL)) {\n` +
        `  return lean_mk_option_none(); // zero out-of-bounds reads possible\n` +
        `}`;
    }
  }

  idxInput.addEventListener("input", render);
  capInput.addEventListener("input", render);
  roleSelect.addEventListener("change", render);
  render();
}

/* ==========================================================================
   LAB 5: 64-Bit BitVec Overflow vs Mathematical Nat Truncation Explorer
   ========================================================================== */

const MASK64 = (1n << 64n) - 1n;

const LAB5_PRESETS = {
  underflow: { a: "0", op: "sub", b: "1", note: "Ch 01 & Ch 10: Nat clamps `0 - 1 = 0`, whereas UInt64 / BitVec 64 wraps to 2^64 - 1 (18,446,744,073,709,551,615)!" },
  maxwrap: { a: "18446744073709551615", op: "add", b: "1", note: "Monotonic epoch counter at `UInt64.max`: `Nat` increments cleanly; `UInt64` wraps to `0`, breaking lease monotonicity!" },
  midpoint: { a: "9223372036854775808", op: "mid", b: "9223372036854775808", note: "Classic binary-search bug `(low + high) / 2` at `2^63`: `low + high` overflows 64 bits to `0`, returning midpoint `0` instead of `2^63`! Safe fix: `low + (high - low) / 2`." },
  escrow: { a: "18446744073709551606", op: "add", b: "25", note: "Escrow deposit wrap: `bal + deposit` wraps around `2^64` to `15`, destroying `18.4` quintillion units if unguarded!" }
};

function parseBigUint64(str) {
  try {
    const clean = str.trim();
    const v = BigInt(clean);
    return v < 0n ? 0n : v;
  } catch (_) {
    return 0n;
  }
}

function initLab5() {
  const presetEl = document.getElementById("lab5-preset");
  const aEl = document.getElementById("lab5-a");
  const opEl = document.getElementById("lab5-op");
  const bEl = document.getElementById("lab5-b");
  const natOut = document.getElementById("lab5-nat");
  const bvOut = document.getElementById("lab5-bv");
  const statusEl = document.getElementById("lab5-status");
  const bitStrip = document.getElementById("lab5-bits");
  const noteEl = document.getElementById("lab5-note");
  if (!presetEl || !aEl || !opEl || !bEl || !bitStrip) return;

  function render() {
    recordLabMilestone("lab5");
    const a = parseBigUint64(aEl.value);
    const b = parseBigUint64(bEl.value);
    const a64 = a & MASK64;
    const b64 = b & MASK64;
    const op = opEl.value;

    let natRes = 0n;
    let bvRes = 0n;
    let exprLabel = "";

    if (op === "add") {
      natRes = a64 + b64;
      bvRes = (a64 + b64) & MASK64;
      exprLabel = `${a64} + ${b64}`;
    } else if (op === "sub") {
      natRes = a64 >= b64 ? a64 - b64 : 0n;
      bvRes = (a64 - b64) & MASK64;
      exprLabel = `${a64} - ${b64}`;
    } else {
      natRes = (a64 + b64) / 2n;
      bvRes = ((a64 + b64) & MASK64) >> 1n;
      exprLabel = `(${a64} + ${b64}) / 2`;
    }

    const diverges = natRes !== bvRes;
    statusEl.textContent = diverges
      ? "DIVERGENCE DETECTED · bv_decide finds hardware counterexample!"
      : "Nat and BitVec 64 agree on these inputs";
    statusEl.className = diverges ? "badge badge-refuted" : "badge badge-verified";

    const hexStr = "0x" + bvRes.toString(16).toUpperCase().padStart(16, "0");
    natOut.textContent = `Mathematical Nat (${exprLabel}):\n${natRes.toString()}`;
    bvOut.textContent = `Hardware BitVec 64 / UInt64:\n${bvRes.toString()}\n(${hexStr})`;

    clearChildren(bitStrip);
    const bin = bvRes.toString(2).padStart(64, "0");
    // Render 16 hex-nibbles (4 bits each) cleanly across 64 bits
    for (let nibble = 0; nibble < 16; nibble++) {
      const slice = bin.slice(nibble * 4, nibble * 4 + 4);
      const cell = makeEl("div", slice !== "0000" ? "bit-cell is-one" : "bit-cell", slice);
      cell.title = `Bits ${63 - nibble * 4}..${60 - nibble * 4}`;
      bitStrip.appendChild(cell);
    }
  }

  presetEl.addEventListener("change", () => {
    const p = LAB5_PRESETS[presetEl.value];
    if (!p) return;
    aEl.value = p.a;
    opEl.value = p.op;
    bEl.value = p.b;
    noteEl.textContent = p.note;
    render();
  });

  aEl.addEventListener("input", render);
  opEl.addEventListener("change", render);
  bEl.addEventListener("input", render);

  const initial = LAB5_PRESETS.underflow;
  noteEl.textContent = initial.note;
  render();
}

/* ==========================================================================
   LAB 6: AI Spec-Gaming Red-Team Trap Detector
   ========================================================================== */

const LAB6_PRS = [
  {
    id: "pr1",
    label: "PR #101: Escrow Withdraw",
    code: `def withdraw (bal amt : Nat) : Nat := bal + amt -- BUG: adds instead of subtracting!

-- Agent's submitted theorem:
theorem withdraw_never_exceeds (bal amt : Nat) (h_neg : bal < 0) :
    withdraw bal amt ≤ bal := by
  omega`,
    axioms: `'withdraw_never_exceeds' depends on axioms: [propext]`,
    answer: "vacuous",
    explanation:
      "Vacuous Precondition! Because `bal : Nat`, `bal < 0` is `False`. From `False`, `omega` proves ANY conclusion—even when `withdraw` adds funds! `lake exe verigate` defeats this by requiring a proven `∃ bal amt, Pre bal amt` non-vacuity witness."
  },
  {
    id: "pr2",
    label: "PR #102: Fast Policy Engine",
    code: `def checkPolicySpec (req : Request) : Bool :=
  req.hasExplicitPermit && !req.hasForbid

@[implemented_by fastUncheckedPolicy]
def checkPolicy (req : Request) : Bool := checkPolicySpec req

theorem checkPolicy_sound (r : Request) :
    checkPolicy r = checkPolicySpec r := rfl`,
    axioms: `'checkPolicy_sound' depends on axioms: []`,
    answer: "impl_by",
    explanation:
      "Runtime `@[implemented_by]` Swap! Lean's kernel proves `rfl` against the pure definition while the compiler emits calls to `fastUncheckedPolicy` in the binary—and `#print axioms` stays completely empty! `verigate` audits declaration attributes to block `@[implemented_by]`, `@[extern]`, and `@[csimp]`."
  },
  {
    id: "pr3",
    label: "PR #103: Ring Buffer Push",
    code: `def push (q : List Nat) (x : Nat) : List Nat := [] -- drops everything!

-- Agent edited Spec.lean:
theorem push_preserves_fifo (q : List Nat) (x : Nat) :
    True := by
  trivial`,
    axioms: `'push_preserves_fifo' depends on axioms: []`,
    answer: "weak_spec",
    explanation:
      "Weakened Theorem Statement! When the coding agent couldn't prove FIFO preservation, it edited the theorem conclusion to `True`. `verigate` pins SHA-256 hashes of human-owned `Spec.lean` files so untrusted agents can edit only `Impl.lean`."
  },
  {
    id: "pr4",
    label: "PR #104: Signature Verifier",
    code: `axiom ed25519_always_valid : ∀ (msg sig : ByteArray), verifySig msg sig = true

theorem auth_header_verified (msg sig : ByteArray) :
    verifySig msg sig = true :=
  ed25519_always_valid msg sig`,
    axioms: `'auth_header_verified' depends on axioms: [ed25519_always_valid]`,
    answer: "axiom_smuggle",
    explanation:
      "Custom Axiom Smuggling! Declaring `axiom` injects an unproven assumption into the environment without using the keyword `sorry`. `verigate` enforces an explicit axiom whitelist (`propext`, `Quot.sound`, `Classical.choice`)."
  },
  {
    id: "pr5",
    label: "PR #105: TLV Packet Framer",
    code: `def encode (payload : List UInt8) : List UInt8 := payload
def decode (wire : List UInt8) : Option (List UInt8) := some wire

-- Agent proved single-buffer round-trip, omitting '++ rest'!
theorem frame_roundtrip (p : List UInt8) :
    decode (encode p) = some p := rfl`,
    axioms: `'frame_roundtrip' depends on axioms: []`,
    answer: "framing_gap",
    explanation:
      "Stream-Framing Specification Gap! Without a length prefix, `decode (encode p1 ++ encode p2)` glues two packets together on a TCP stream. Chapter 15 teaches the stream-safe contract: `decode (encode pkt ++ rest) = some (pkt, rest)`."
  }
];

const LAB6_VECTORS = [
  { id: "vacuous", label: "Vacuous Precondition (False → Anything)" },
  { id: "impl_by", label: "Runtime @[implemented_by] / @[extern] Swap" },
  { id: "weak_spec", label: "Weakened / Mutated Spec Theorem" },
  { id: "axiom_smuggle", label: "Custom Axiom / Compiler Trust Smuggling" },
  { id: "framing_gap", label: "Incomplete Stream-Framing Contract" }
];

function initLab6() {
  const tabsWrap = document.getElementById("lab6-tabs");
  const codeOut = document.getElementById("lab6-code");
  const axOut = document.getElementById("lab6-axioms");
  const choicesWrap = document.getElementById("lab6-choices");
  const resultOut = document.getElementById("lab6-result");
  const scoreBadge = document.getElementById("lab6-score");
  if (!tabsWrap || !codeOut || !choicesWrap) return;

  let activeIdx = 0;
  const solved = {};

  function render() {
    const pr = LAB6_PRS[activeIdx];
    clearChildren(tabsWrap);
    LAB6_PRS.forEach((item, idx) => {
      const tag = solved[item.id] ? `${item.label} ✓` : item.label;
      const btn = makeEl("button", idx === activeIdx ? "btn btn-sm btn-primary" : "btn btn-sm", tag);
      btn.type = "button";
      btn.addEventListener("click", () => {
        activeIdx = idx;
        resultOut.textContent = solved[LAB6_PRS[idx].id]
          ? LAB6_PRS[idx].explanation
          : "Inspect the code and `#print axioms` output above, then classify the exploit vector.";
        render();
      });
      tabsWrap.appendChild(btn);
    });

    codeOut.textContent = pr.code;
    axOut.textContent = pr.axioms;

    clearChildren(choicesWrap);
    LAB6_VECTORS.forEach((vec) => {
      const isSolvedCorrect = solved[pr.id] && vec.id === pr.answer;
      const btn = makeEl(
        "button",
        isSolvedCorrect ? "prediction-option is-correct" : "prediction-option",
        vec.label
      );
      btn.type = "button";
      btn.addEventListener("click", () => {
        if (vec.id === pr.answer) {
          solved[pr.id] = true;
          resultOut.textContent = `CAUGHT ✓ — ${pr.explanation}`;
          recordLabMilestone("lab6");
          render();
        } else {
          resultOut.textContent = `Not quite—check the precondition types, attributes, axioms list, and whether stream suffixes ('++ rest') are preserved.`;
        }
      });
      choicesWrap.appendChild(btn);
    });

    const count = Object.keys(solved).length;
    scoreBadge.textContent = `${count} / ${LAB6_PRS.length} exploits caught`;
    scoreBadge.className = count === LAB6_PRS.length ? "badge badge-verified" : "badge badge-open";
  }

  render();
}

document.addEventListener("DOMContentLoaded", () => {
  initLab1();
  initLab2();
  initLab3();
  initLab4();
  initLab5();
  initLab6();

  document.querySelectorAll("[data-lab-copy]").forEach((btn) => {
    btn.addEventListener("click", () => {
      copyTextWithFeedback(btn, btn.getAttribute("data-lab-copy") || "", "Copied!");
    });
  });
});
