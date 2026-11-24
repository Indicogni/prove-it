# Study Guide: Part I & Part II (Chapters 1–8 & Checkpoints 1–2)

> **How to use this guide**
> 1. Open the starter file in `ProveIt/` (or paste it into `live.lean-lang.org`).
> 2. Read the Socratic prompt below *before* touching `sorry`—predict what invariant or edge case is doing the real work.
> 3. Expand **Hint 1 (Nudge)** first, **Hint 2 (Strategy)** only after 5 minutes of active struggle, and **Hint 3 (Blueprint)** only to unblock syntax.
> 4. Before moving on, answer **"Check your explanation"** out loud in plain engineering language—no Lean jargon allowed!

---

## Part I: Types, Domain Modeling, Exhaustion & Bounded Model Checking

### Chapter 1 — The Silent Truncation Bug (`ProveIt/Ch01.lean`)

**Socratic Warm-Up**
- An engineer writes `let next := remaining - cost; if next ≥ 0 then some next else none` where `remaining` and `cost` have type `Nat`. Why does `chargeQuotaBuggy 0 500` return `some 0` instead of `none`?
- Why does Lean define `(0 : Nat) - 1 = 0` rather than raising a runtime exception or wrapping around to `2^64 - 1`?

#### Progressive Hints (`Ch01.lean`)

- **Exercise 1.1 (`chargeQuotaOpt_zero_rejects`)**
  <details><summary>Hint 1 — Nudge</summary>
  Open <code>chargeQuotaOpt</code> so Lean can see the <code>if cost ≤ 0</code> branch condition alongside your hypothesis <code>hPos : 0 &lt; cost</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Use <code>unfold chargeQuotaOpt</code> followed by <code>split</code>. In the <code>then</code> branch, <code>cost ≤ 0</code> contradicts <code>0 &lt; cost</code>; in the <code>else</code> branch, both sides are <code>none</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold chargeQuotaOpt; split; · omega; · rfl</code>
  </details>

- **Exercise 1.2 (`balanceAfter_negative_on_overdraft`)**
  <details><summary>Hint 1 — Nudge</summary>
  Unlike <code>Nat</code>, subtraction on <code>Int</code> never truncates at zero—linear arithmetic holds without side conditions.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold <code>balanceAfter</code> so <code>omega</code> sees <code>remaining - cost &lt; 0</code> directly from <code>hOver : remaining &lt; cost</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold balanceAfter; omega</code>
  </details>

- **Exercises 1.3a & 1.3b (`chargeWithReserve` & `chargeWithReserve_sound`)**
  <details><summary>Hint 1 — Nudge</summary>
  Avoid writing <code>reserve ≤ remaining - cost</code> as your guard! Think what happens when <code>reserve = 0</code>, <code>remaining = 0</code>, and <code>cost = 1</code>: <code>0 ≤ 0 - 1</code> evaluates to <code>true</code> on <code>Nat</code>! Write the guard using addition instead.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Guard with <code>if cost + reserve ≤ remaining then some (remaining - cost) else none</code>. In <code>chargeWithReserve_sound</code>, unfold <code>chargeWithReserve at h</code>, <code>split at h</code>, extract <code>next</code> with <code>injection h with hNext</code>, and discharge the arithmetic conjunction with <code>omega</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold chargeWithReserve at h; split at h; · injection h with hNext; omega; · nomatch h</code>
  </details>

**Check your explanation**
> *Explain to a teammate why rewriting a subtraction guard `a - b ≥ c` into an addition guard `a ≥ b + c` eliminates silent underflow bugs on unsigned/natural types—even at `c = 0`.*

---

### Chapter 2 — Illegal States & Domain Modeling (`ProveIt/Ch02.lean`)

**Socratic Warm-Up**
- `RawSession` has three `Bool` fields and two `Option` fields. How many distinct combinations can exist at runtime, and why did `zombieSession` bypass `rawBearerToken`'s check?
- Why did we group `.active`'s three fields inside a dedicated `ActiveGrant` structure instead of writing `| active (principalId : String) (sessionToken : Nat) (expiresAt : Nat)` directly on `SessionState`?

#### Progressive Hints (`Ch02.lean`)

- **Exercise 2.1 (`revokeSession`)**
  <details><summary>Hint 1 — Nudge</summary>
  Match exhaustively on all four constructors of <code>SessionState</code>. Pay close attention to the audit rule when a session is already <code>.revoked pid originalReason</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Map <code>.anonymous</code> to <code>.anonymous</code>, both <code>.pendingMfa pid _</code> and <code>.active grant</code> to <code>.revoked ... reason</code>, and preserve <code>originalReason</code> on <code>.revoked pid originalReason</code>. Prove the three concrete examples with <code>rfl</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  Each <code>example</code> after implementing <code>revokeSession</code> closes with <code>rfl</code>.
  </details>

- **Exercise 2.2 (`revokeSession_clears_bearer`)**
  <details><summary>Hint 1 — Nudge</summary>
  Can <code>revokeSession</code> ever return an <code>.active</code> constructor on any of the four input variants?
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Split <code>s</code> into its four constructors with <code>cases s</code>. On every constructor, <code>bearerToken (revokeSession _ reason) now</code> reduces definitionally to <code>none</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>cases s &lt;;&gt; rfl</code>
  </details>

- **Exercise 2.3 (`bearerToken_some_unexpired`)**
  <details><summary>Hint 1 — Nudge</summary>
  Three of the four constructors of <code>SessionState</code> make <code>h : none = some tok</code>, which <code>nomatch h</code> refutes immediately.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Use <code>cases s</code>. In the <code>active grant</code> case, run <code>dsimp [bearerToken] at h</code> to reduce the pattern match, then <code>split at h</code> on <code>now &lt; grant.expiresAt</code>. Extract <code>grant.sessionToken = tok</code> with <code>injection h with hTok</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>cases s with | active grant =&gt; dsimp [bearerToken] at h; split at h; · injection h with hTok; exact ⟨grant, rfl, hTok, ‹now &lt; grant.expiresAt›⟩; · nomatch h | _ =&gt; nomatch h</code>
  </details>

**Check your explanation**
> *Why did `revokeSession_clears_bearer` verify infinitely many principal strings and timestamps in four case splits without needing a single loop or property-based fuzzer?*

---

### Chapter 3 — Compile-Time Exhaustion & Boolean Reflection (`ProveIt/Ch03.lean`)

**Socratic Warm-Up**
- In `checkAccessBuggy`, how did writing a negative filter (`action != .deleteCluster`) for `.auditor` violate least privilege?
- What is the operational difference between `checkAccess : Role → Action → Bool` and `Allowed : Role → Action → Prop`, and why do high-assurance systems like Cedar maintain both?

#### Progressive Hints (`Ch03.lean`)

- **Exercise 3.1 (`viewer_least_privilege`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>Action</code> has only four inhabitants. If <code>h</code> is moved back into the goal arrow before case-splitting on <code>action</code>, each of the four subgoals becomes a closed, decidable implication.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Run <code>revert h</code> so the goal becomes <code>checkAccess .viewer action = true → action = .readMetrics</code>, then split on <code>cases action</code> and evaluate all four cases at compile time.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>revert h; cases action &lt;;&gt; decide</code>
  </details>

- **Exercises 3.2a & 3.2b (`checkAccess_implies_allowed` & `checkAccess_iff_allowed`)**
  <details><summary>Hint 1 — Nudge</summary>
  Every <code>true</code> branch of <code>checkAccess</code> corresponds directly to one of the four constructors of <code>Allowed</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Either pattern-match on <code>role, action, h</code> directly (Lean's equation compiler automatically rules out pairs where <code>checkAccess</code> is <code>false</code>), or run <code>cases role &lt;;&gt; cases action</code> and close impossible branches with <code>nomatch h</code>. Then pair both directions with <code>⟨checkAccess_implies_allowed role action, allowed_implies_checkAccess role action⟩</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 3.2a: <code>cases role &lt;;&gt; cases action</code>, closing valid cells with <code>exact .allReadMetrics _</code> / <code>.deployerDeploy</code> / <code>.auditorReadAudit</code> / <code>.adminAll _</code> and invalid cells with <code>nomatch h</code>. In 3.2b: <code>exact ⟨checkAccess_implies_allowed role action, allowed_implies_checkAccess role action⟩</code>.
  </details>

- **Exercise 3.3 (`separation_of_duty`)**
  <details><summary>Hint 1 — Nudge</summary>
  Because <code>instDecidableAllowed</code> was registered right above Exercise 3.3, Lean now knows how to evaluate <code>Allowed role action</code> at compile time for every concrete <code>Role</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Move <code>hNonAdmin</code> back into the goal with <code>revert hNonAdmin</code>, split into the four roles with <code>cases role</code>, and let <code>decide</code> verify all four roles.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>revert hNonAdmin; cases role &lt;;&gt; decide</code>
  </details>

**Check your explanation**
> *Suppose a fifth action `rotateKeys` is added to `Action` next quarter. Walk through what happens at compile time to `checkAccess`, `Allowed`, and `checkAccess_iff_allowed`—and why silent policy drift cannot slip into production.*

---

### Chapter 4 — Gear 1: A TLA+ Model Checker in 35 Lines (`ProveIt/Ch04.lean`)

**Socratic Warm-Up**
- Why did `bfsLoop` find the 5-step split-brain counterexample instead of a 9-step redundant trace? Which property of breadth-first search guarantees minimal-length counterexamples?
- Why does checking the lease on the *lock server* fail to prevent stale overwrites, whereas checking a monotonic *fencing token* at the *storage server* succeeds?

#### Progressive Hints (`Ch04.lean`)

- **Exercise 4.1 (`splitBrainTrace_violates_safety`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>runTrace unfencedStep initLockState splitBrainTrace</code> is a concrete computation with no free variables—Lean can evaluate the exact final state for you!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Use <code>refine ⟨_, rfl, ?_⟩</code>: unifying the first conjunction slot with <code>rfl</code> forces the existential witness <code>_</code> to evaluate to the concrete <code>sFinal</code>, leaving a concrete <code>lockSafe sFinal = false</code> goal.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>refine ⟨_, rfl, ?_⟩; rfl</code>
  </details>

- **Exercise 4.2 (`fencedWrite`)**
  <details><summary>Hint 1 — Nudge</summary>
  Compare <code>fencedWrite</code> against the <code>.write n</code> arm of <code>unfencedStep</code>: instead of setting <code>staleOverwrite := true</code> when <code>tok &lt; s.storageEpoch</code>, storage must reject the request with <code>none</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Match on <code>cachedEpochOf s n</code>. On <code>none</code>, return <code>none</code>. On <code>some tok</code>, check <code>if s.storageEpoch ≤ tok then some { s with storageEpoch := tok } else none</code>. Then replace the <code>sorry</code> on the <code>bfsViolation</code> example with <code>rfl</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>match cachedEpochOf s n with | none =&gt; none | some tok =&gt; if s.storageEpoch ≤ tok then some { s with storageEpoch := tok } else none</code>
  </details>

- **Exercises 4.3a & 4.3b (`fencedWrite_epoch_monotone` & `fencedWrite_preserves_safe`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>fencedWrite</code> has two nested branches: first <code>match cachedEpochOf s n</code>, then <code>if s.storageEpoch ≤ tok</code>. Only one path returns <code>some ...</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold <code>fencedWrite at h</code> (or <code>hStep</code>), run <code>split at h</code> for the <code>Option</code> match, and run <code>split at h</code> again on the <code>some tok</code> arm. Use <code>injection ... with hEq</code> and <code>rw [← hEq]</code> to substitute <code>s'</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold fencedWrite at h; split at h; · nomatch h; · split at h; · injection h with hEq; rw [← hEq]; omega; · nomatch h</code> (and <code>exact hSafe</code> in 4.3b).
  </details>

**Check your explanation**
> *What did `bfsViolation` verify about `fencedStep` that unit tests usually miss, and what limitation of `bfsViolation` (`nextEpoch ≤ 2`, `fuel = 500`) motivated proving `fencedWrite_epoch_monotone` symbolically?*

---

### Checkpoint 1 — Zero-Panic Rollout & Canary Router (`ProveIt/Checkpoints/Cp1.lean`)

**Socratic Warm-Up**
- What would `{ stablePct := 100 - desiredPct, canaryPct := desiredPct }` compute if an operator passed `desiredPct = 150`? How does clamping `desiredPct` to `100` before subtracting keep `stablePct + canaryPct = 100` across all `Nat` inputs?

#### Progressive Hints (`Checkpoints/Cp1.lean`)

- **Tasks 1.1–1.3 (`trafficSplit`, `trafficSplit_sums_to_100`, `unhealthy_canary_sheds_traffic`)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>.canary desiredPct errorCount</code>, check <code>errorCount ≤ errorBudget</code> first; inside the healthy branch, bind <code>let c := if desiredPct ≤ 100 then desiredPct else 100</code> and construct <code>{ stablePct := 100 - c, canaryPct := c }</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>trafficSplit_sums_to_100</code>, split on <code>cases phase</code>. Three constructors close with <code>rfl</code>; on <code>canary</code>, use <code>dsimp [trafficSplit]</code>, <code>split</code> on <code>errorCount ≤ errorBudget</code>, <code>dsimp</code> to project struct fields, and <code>split &lt;;&gt; omega</code> on <code>desiredPct ≤ 100</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For Task 1.3: <code>dsimp [trafficSplit]; split; · omega; · rfl</code>.
  </details>

- **Tasks 1.4 & 1.5 (`checkPromote_iff_canPromote` & `stepRollout_preserves_healthy`)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>checkPromote</code>, only one of the six <code>(Env, Approval)</code> pairs is forbidden: <code>(.prod, .ciGreen)</code>. In Task 1.5, <code>PhaseHealthy</code> reduces to <code>True</code> (closed by <code>trivial</code>) on every phase except <code>.canary</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  For Task 1.4, use <code>constructor</code> to split <code>↔</code> into forward and backward directions, matching Chapter 3's pattern. For Task 1.5, match on <code>phase, ev</code>: on <code>.stable, .startCanary _</code>, <code>0 ≤ errorBudget</code> closes by <code>omega</code>; on <code>.canary _ errs, .recordError</code>, <code>dsimp [stepRollout]; split</code> separates <code>errs + 1 ≤ errorBudget</code> from the rollback branch.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  On <code>.canary _ errs, .recordError</code>: <code>dsimp [stepRollout]; split; · dsimp [PhaseHealthy]; omega; · trivial</code>.
  </details>

**Check your explanation**
> *Walk through the two independent places where an unhealthy canary (`errorBudget < errorCount`) is contained in this design: once in data-plane routing (`trafficSplit`) and once in control-plane transitions (`stepRollout`).*

---

## Part II: Tactics, Control Flow, Stuck-Goal Triage & Unbounded Invariants

### Chapter 5 — Proofs Are Programs, Goals Are Stack Traces (`ProveIt/Ch05.lean`)

**Socratic Warm-Up**
- When your Infoview shows `hGate : A ∧ B → C` above `⊢` and `C` below `⊢`, what does `apply hGate` change the goal below `⊢` into, and why does that mirror calling `hGate(...)` backwards from its return type?
- Why is `¬ P` defined in Lean as the function type `P → False` rather than a primitive boolean negation?

#### Progressive Hints (`Ch05.lean`)

- **Exercise 5.1 (`uncurry_webhook_gate`)**
  <details><summary>Hint 1 — Nudge</summary>
  Bring both antecedents into your local context with <code>intro</code>, then call <code>hGate</code> backwards.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Run <code>intro hSig hFresh</code>, <code>apply hGate</code>, and split the resulting conjunction goal <code>SigValid req ∧ TimestampFresh req</code> with <code>constructor</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>intro hSig hFresh; apply hGate; constructor; · exact hSig; · exact hFresh</code>
  </details>

- **Exercise 5.2 (`idempotent_ack`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>hOutcome : AlreadySeen req ∨ EnqueueJob req</code> is a sum type—you must handle both possible tags.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unpack the disjunction with <code>rcases hOutcome with hSeen | hJob</code>, applying <code>hCached</code> in the first branch and <code>hEnqueued</code> in the second.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>rcases hOutcome with hSeen | hJob; · exact hCached hSeen; · exact hEnqueued hJob</code>
  </details>

- **Exercises 5.3a, 5.3b & 5.4 (`stale_webhook_rejected`, `fresh_and_expired_disjoint`, `webhook_audit_witness`)**
  <details><summary>Hint 1 — Nudge</summary>
  Whenever the goal below <code>⊢</code> starts with <code>¬ ...</code>, start with <code>intro</code>: proving <code>¬ Q</code> means assuming <code>Q</code> and deriving <code>False</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In 5.3a, <code>intro hEnq</code>, then pass <code>hMustBeFresh hEnq</code> into <code>hNotFresh</code>. In 5.3b, <code>intro ⟨hFresh, hExpired⟩</code>, unfold both predicates, and call <code>omega</code>. In 5.4, specialize <code>hGate req ⟨hSig, hFresh⟩</code>, then unpack <code>hAudit req ...</code> with <code>rcases</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 5.4: <code>have hEnq := hGate req ⟨hSig, hFresh⟩; exact hAudit req hEnq</code> (or unpack and rebuild with <code>rcases</code>).
  </details>

**Check your explanation**
> *Translate each of `P → Q`, `P ∧ Q`, `P ∨ Q`, `¬ P`, and `∃ x, P x` into an everyday programming construct (function, struct, tagged union, uninhabited return type, dependent pair).*

---

### Chapter 6 — Control Flow, Rewriting & Linear Arithmetic (`ProveIt/Ch06.lean`)

**Socratic Warm-Up**
- Why is `fun_cases settleQuota q actual` less brittle than manually chaining `unfold settleQuota; split` when functions grow additional `else if` clauses?
- Why do production Lean codebases prefer `simp only [QuotaBucket.total]` over an unrestricted `simp` call?

#### Progressive Hints (`Ch06.lean`)

- **Exercise 6.1 (`nextBackoffMs_bounded`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>nextBackoffMs</code> is a thin wrapper around <code>clampBackoffMs</code>, whose bounds theorem <code>clampBackoffMs_in_bounds</code> is already proven above!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Either unfold <code>nextBackoffMs</code> and apply <code>clampBackoffMs_in_bounds (prevMs * 2 + 10) minMs maxMs hValid</code>, or invoke <code>grind</code> directly (since both functions carry <code>@[grind =]</code>).
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold nextBackoffMs; exact clampBackoffMs_in_bounds (prevMs * 2 + 10) minMs maxMs hValid</code> (or <code>grind</code>).
  </details>

- **Exercise 6.2 (`settleQuota_preserves_total`)**
  <details><summary>Hint 1 — Nudge</summary>
  Check the overrun branch (<code>q.reserved &lt; actual</code>) on paper first: <code>(q.used + q.reserved) + 0 + q.available</code> still equals <code>q.used + q.reserved + q.available</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Branch along <code>settleQuota q actual</code> using <code>fun_cases settleQuota q actual</code>, expand only <code>QuotaBucket.total</code> with <code>simp only [QuotaBucket.total]</code>, and finish both branches with <code>omega</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>fun_cases settleQuota q actual &lt;;&gt; simp only [QuotaBucket.total] &lt;;&gt; omega</code>
  </details>

- **Exercise 6.3 (`effectiveRps_respects_all_caps`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>PlanTier</code>, <code>tierLimitRps</code>, and <code>effectiveRps</code> are all annotated with <code>@[grind =]</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Call <code>grind</code> directly—or if practicing manual control flow, run <code>fun_cases effectiveRps tier requestedRps clusterCeiling &lt;;&gt; omega</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>grind</code>
  </details>

**Check your explanation**
> *When `grind` closes a 3-way conjunction over nested `if` branches in one word, what three reasoning engines is it combining under the hood—and why does Lean's kernel still check the generated proof term with zero trust in `grind`'s C++ implementation?*

---

### Chapter 7 — Unprovable on Purpose: Stuck-Infoview Triage (`ProveIt/Ch07.lean`)

**Socratic Warm-Up**
- Look at the three stuck Infoview states in Chapter 7 before writing a single tactic:
  1. `hBal : balance ≤ maxBalance, hCond : refund ≤ maxBalance ⊢ balance + refund ≤ maxBalance`
  2. `cursor capacity : Nat ⊢ (cursor + 1) % capacity < capacity`
  3. `hWeak : s.completed ≤ s.submitted, hPos : 0 < s.inFlight ⊢ s.completed + 1 ≤ s.submitted`
- How can you tell—purely by testing whether your counterexample state is reachable from `init`—the difference between **Case 1 (buggy code)** and **Case 3 (too-weak invariant)**?

#### Progressive Hints (`Ch07.lean`)

- **Exercises 7.1a & 7.1b (`creditRefundBuggy_overflows_cap` & `creditRefundFixed_spec`)**
  <details><summary>Hint 1 — Nudge</summary>
  In 7.1a, pick any concrete numbers with <code>balance ≤ maxBalance</code> and <code>refund ≤ maxBalance</code> whose sum exceeds <code>maxBalance</code> (such as <code>80, 50, 100</code>). In 7.1b, check <code>balance + refund ≤ maxBalance</code> instead of <code>refund ≤ maxBalance</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Supply <code>refine ⟨80, 50, 100, ?_, ?_⟩ &lt;;&gt; decide</code> for 7.1a. After implementing <code>creditRefundFixed</code>, prove <code>creditRefundFixed_spec</code> with <code>fun_cases creditRefundFixed balance refund maxBalance &lt;;&gt; omega</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 7.1b: <code>if balance + refund ≤ maxBalance then balance + refund else maxBalance</code>, then <code>fun_cases creditRefundFixed balance refund maxBalance &lt;;&gt; omega</code>.
  </details>

- **Exercises 7.2a & 7.2b (`ringNextSlot_unconditional_false` & `ringNextSlot_lt_capacity`)**
  <details><summary>Hint 1 — Nudge</summary>
  Instantiate the false universal hypothesis <code>hAll</code> at <code>cursor = 0</code> and <code>capacity = 0</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In 7.2a, <code>intro hAll</code>, bind <code>have hZero : ringNextSlot 0 0 &lt; 0 := hAll 0 0</code>, and close with <code>nomatch hZero</code>. In 7.2b, unfold <code>ringNextSlot</code> and apply <code>Nat.mod_lt (cursor + 1) hPos</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 7.2b: <code>unfold ringNextSlot; exact Nat.mod_lt (cursor + 1) hPos</code>.
  </details>

- **Exercises 7.3a & 7.3b (`weakSafety_not_inductive` & `StrongInv`)**
  <details><summary>Hint 1 — Nudge</summary>
  In 7.3a, instantiate <code>hStep</code> at <code>{ submitted := 5, completed := 5, inFlight := 1 }</code>. In 7.3b, notice that every <code>onSubmit</code> adds 1 to both <code>submitted</code> and <code>inFlight</code>, while every active <code>onComplete</code> moves 1 from <code>inFlight</code> to <code>completed</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Define <code>def StrongInv (s : TrackerState) : Prop := s.completed + s.inFlight = s.submitted</code>. Remember to use <code>dsimp [StrongInv, onSubmit] at *</code> (rather than bare <code>unfold</code>) so struct field projections reduce before calling <code>omega</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In <code>strongInv_onComplete</code>: <code>fun_cases onComplete s &lt;;&gt; dsimp [StrongInv] at * &lt;;&gt; omega</code>.
  </details>

**Check your explanation**
> *You are reviewing a teammate's stuck Lean proof at 4 PM. List the 3-step diagnostic checklist you run on the Infoview goal before spending an hour searching for library lemmas.*

---

### Chapter 8 — Gear 2: Inductive Invariants & Strengthening (`ProveIt/Ch08.lean`)

**Socratic Warm-Up**
- Why is `edenWireState` (`coordinatorHasAuthority = false, inFlightGrants = 1, activeLeaders = 1`) called a "Garden-of-Eden" state? Can the cluster ever reach `edenWireState` starting from `Init`?
- Why isn't `inFlightGrants + activeLeaders ≤ 1` inductive on its own without also including `(if s.coordinatorHasAuthority then 1 else 0)` in `TokenInvariant`? (Hint: test `Next.dispatchGrant`!)

#### Progressive Hints (`Ch08.lean`)

- **Exercise 8.1 (`eden_breaks_naive_induction`)**
  <details><summary>Hint 1 — Nudge</summary>
  Split the conjunction with <code>constructor</code>. For the existential witness, apply constructor <code>Next.deliverGrant edenWireState</code> directly!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  The left side <code>SafeMutualExclusion edenWireState</code> closes by <code>decide</code>. On the right side, use <code>refine ⟨_, Next.deliverGrant edenWireState (by decide), ?_⟩</code>, then close <code>¬ SafeMutualExclusion _</code> with <code>decide</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>constructor; · decide; · refine ⟨_, Next.deliverGrant edenWireState (by decide), ?_⟩; decide</code>
  </details>

- **Exercises 8.2a & 8.2b (`tokenInvariant_implies_safety` & `tokenInvariant_next`)**
  <details><summary>Hint 1 — Nudge</summary>
  In 8.2a and 8.2b, <code>authorityCount</code> contains <code>if s.coordinatorHasAuthority then 1 else 0</code>. Case-splitting on the boolean <code>s.coordinatorHasAuthority</code> turns that <code>if</code> into concrete <code>1</code> or <code>0</code> for <code>omega</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In 8.2b, run <code>cases hNext</code> to handle all four protocol transitions (<code>dispatchGrant</code>, <code>deliverGrant</code>, <code>relinquish</code>, <code>dropGrant</code>). On each branch, reduce projections with <code>dsimp [TokenInvariant, authorityCount] at *</code> and split <code>cases hAuth : s.coordinatorHasAuthority &lt;;&gt; simp only [hAuth] at * &lt;;&gt; omega</code> (or use <code>cases hNext &lt;;&gt; grind</code>!).
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 8.2a: <code>dsimp [TokenInvariant, authorityCount, WireAndLeaderBound, SafeMutualExclusion] at *; split at hInv &lt;;&gt; omega</code>. In 8.2b: <code>cases hNext &lt;;&gt; grind</code> (or explicit 4-case <code>dsimp</code> + <code>omega</code>).
  </details>

- **Exercises 8.3a & 8.3b (`reachable_tokenInvariant` & `reachable_mutual_exclusion`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>Reachable</code> is an inductive predicate with two constructors: <code>init</code> (proved by <code>tokenInvariant_init</code>) and <code>step</code> (proved by <code>tokenInvariant_next</code>!).
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In 8.3a, run <code>induction hReach with | init hInit =&gt; exact tokenInvariant_init hInit | step _ hNext ih =&gt; exact tokenInvariant_next ih hNext</code>. In 8.3b, chain <code>reachable_tokenInvariant</code> into <code>tokenInvariant_implies_safety</code> and project <code>.right</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In 8.3b: <code>exact (tokenInvariant_implies_safety s (reachable_tokenInvariant hReach)).right</code>.
  </details>

**Check your explanation**
> *Explain why proving a weaker statement (`SafeMutualExclusion`) over `Reachable` can be impossible by direct induction, whereas proving a stronger statement (`TokenInvariant`) goes through cleanly.*

---

### Checkpoint 2 — Crash-Safe Idempotent Write-Ahead Ledger (`ProveIt/Checkpoints/Cp2.lean`)

**Socratic Warm-Up**
- Why did we decompose replay idempotency into two small helper lemmas (`applyEntry_marks_seen` and `applyEntry_of_seen`) instead of unfolding `applyEntry (applyEntry s entry) entry` all at once? What happens to the expression size if you unfold nested `if-else` calls twice?
- Why do we write `induction wal generalizing s` in `replayWal_conserves_funds` instead of plain `induction wal`?

#### Progressive Hints (`Checkpoints/Cp2.lean`)

- **Tasks 2.1, 2.2a & 2.2b (`applyEntry`, `applyEntry_marks_seen`, `applyEntry_of_seen`, `applyEntry_idempotent`)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>applyEntry_marks_seen</code>, every branch either already satisfies <code>entry.txId ∈ s.appliedIds</code> or prepends <code>entry.txId :: s.appliedIds</code>. Do NOT unfold <code>applyEntry</code> inside <code>applyEntry_idempotent</code>—use your two helper lemmas!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Prove <code>applyEntry_marks_seen</code> with <code>fun_cases applyEntry s entry</code>, using <code>assumption</code> on branch 1 and <code>simp only [List.mem_cons, true_or]</code> on branches 2 and 3. Prove <code>applyEntry_of_seen</code> with <code>unfold applyEntry; simp only [hSeen, ↓reduceIte]</code>. Then <code>applyEntry_idempotent</code> is a single call applying <code>applyEntry_of_seen</code> to <code>applyEntry_marks_seen s entry</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In <code>applyEntry_idempotent</code>: <code>exact applyEntry_of_seen (applyEntry s entry) entry (applyEntry_marks_seen s entry)</code>.
  </details>

- **Tasks 2.3, 2.4 & 2.5 (`applyEntry_conserves_funds`, `replayWal_conserves_funds`, `reachable_ledger_conserves`)**
  <details><summary>Hint 1 — Nudge</summary>
  Notice <code>replayWal</code> updates the accumulator state from <code>s</code> to <code>applyEntry s entry</code> on each recursive step—so your induction hypothesis <code>ih</code> must work for *any* starting state <code>s</code> (<code>generalizing s</code>).
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Prove Task 2.3 with <code>fun_cases applyEntry s entry &lt;;&gt; simp only [LedgerState.totalFunds] &lt;;&gt; omega</code>. In Task 2.4, run <code>induction wal generalizing s</code>; in the <code>cons entry rest ih</code> case, <code>dsimp [replayWal]</code>, rewrite with <code>ih (applyEntry s entry)</code>, and finish with <code>applyEntry_conserves_funds</code>. In Task 2.5, run <code>induction hReach</code> and <code>cases hNext</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In Task 2.5's <code>step _ hNext ih</code> case: <code>cases hNext with | processEntry entry =&gt; rw [applyEntry_conserves_funds, ih] | replayBatch wal =&gt; rw [replayWal_conserves_funds, ih]</code>.
  </details>

**Check your explanation**
> *Suppose next month `applyEntry` adds a fourth branch charging a 1% settlement fee into a third account field, or adds a timestamp check before rejecting. Which proof breaks if you proved `applyEntry_idempotent` by brute-force nested case-splitting, versus proving it from `applyEntry_marks_seen` and `applyEntry_of_seen`?*
