# Study Guide: Part III & Part IV (Chapters 9–16 & Checkpoints 3–4)

> **How to use this guide**
> 1. Open the starter file in `ProveIt/` (or paste it into `live.lean-lang.org`).
> 2. Read the Socratic prompt below *before* touching `sorry`—predict what invariant or edge case is doing the real work.
> 3. Expand **Hint 1 (Nudge)** first, **Hint 2 (Strategy)** only after 5 minutes of active struggle, and **Hint 3 (Blueprint)** only to unblock syntax.
> 4. Before moving on, answer **"Check your explanation"** out loud in plain engineering language—no Lean jargon allowed!

---

## Part III: Verified Data, Hardware Arithmetic, Effects & Refinement

### Chapter 9 — Packing Proofs into Types (`ProveIt/Ch09.lean`)

**Socratic Warm-Up**
- Why does `if c < cap then ⟨c, ...⟩` fail to type-check when constructing a `Fin cap`, whereas `if h : c < cap then ⟨c, h⟩` succeeds?
- At runtime in compiled C/machine code, how many extra bytes does `{ bps : Nat // bps ≤ 10_000 }` allocate compared to a bare `Nat`? Why?

#### Progressive Hints (`Ch09.lean`)

- **Exercises 1 & 2 (`clampBps` & `clampBps_idempotent`)**
  <details><summary>Hint 1 — Nudge</summary>
  Use dependent <code>if h : n ≤ 10_000 then ... else ...</code> so the <code>then</code> branch receives <code>h : n ≤ 10_000</code>. Two subtype values are equal whenever their <code>.val</code> fields are equal.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Start <code>clampBps_idempotent</code> with <code>apply Subtype.ext</code>, unfold <code>clampBps</code>, and <code>split</code> on the dependent <code>if</code>. In the <code>else</code> branch, extract <code>b.property : b.val ≤ 10_000</code> to contradict <code>¬ b.val ≤ 10_000</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>apply Subtype.ext; unfold clampBps; split; · rfl; · have := b.property; omega</code>
  </details>

- **Exercise 3 (`fee_le_principal`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>omega</code> handles linear arithmetic, while <code>principal * rate.val</code> multiplies two variables. Bound <code>principal * rate.val ≤ principal * 10_000</code> first!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Use <code>Nat.mul_le_mul_left principal rate.property</code>, then divide both sides by <code>10_000</code> using <code>Nat.div_le_div_right</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>have hMul := Nat.mul_le_mul_left principal rate.property</code>, then <code>have hDiv := Nat.div_le_div_right (c := 10_000) hMul</code>, followed by <code>omega</code>.
  </details>

- **Exercises 4, 5 & 6 (`tryAcquire`, `tryAcquire_spec`, `NonEmptyList.append`)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>tryAcquire_spec</code>, only one branch of <code>tryAcquire</code> returns <code>some ...</code>; the <code>none</code> branch closes immediately with <code>nomatch hAcq</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold <code>tryAcquire</code> at <code>hAcq</code>, <code>split at hAcq</code>, use <code>injection hAcq with hNext</code> and <code>subst hNext</code>. For <code>NonEmptyList.append</code>, keep <code>xs.head</code> as the new head and append <code>ys.toList</code> onto <code>xs.tail</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In <code>tryAcquire_spec</code>: <code>unfold tryAcquire at hAcq; split at hAcq; · injection hAcq with hNext; subst hNext; exact ⟨‹used.val &lt; cap›, rfl⟩; · nomatch hAcq</code>. In <code>toList_append</code>: <code>rfl</code>!
  </details>

**Check your explanation**
> *Explain to a teammate why moving `rate ≤ 10_000` from a runtime `if` check inside every billing helper into `abbrev BasisPoints := { bps : Nat // bps ≤ 10_000 }` eliminates both defensive branches AND proof boilerplate—without adding a single byte of heap allocation.*

---

### Chapter 10 — 64-Bit Hardware Truth (`UInt64` & `BitVec`) (`ProveIt/Ch10.lean`)

**Socratic Warm-Up**
- Why can a property-based test suite run 100,000,000 random cases in `[0 .. 10^9]` on `price + fee ≤ balance` and report 0 failures, yet fail catastrophically in production on `u64`?
- Why does `bv_decide` require unfolding user-defined functions (`unfold myFn`) before bit-blasting?

#### Progressive Hints (`Ch10.lean`)

- **Exercises 1–4 (`saturatingAdd64` & `safeRefill`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>BitVec.uaddOverflow a b</code> returns <code>true</code> precisely when unsigned 64-bit <code>a + b ≥ 2^64</code>. Clamp to <code>maxU64</code> on overflow before comparing against <code>cap</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In both theorems (<code>saturatingAdd64_no_drop</code> and <code>safeRefill_bounds</code>), unfold your custom definitions (including <code>maxU64</code>) so the goal contains only primitive <code>BitVec 64</code> operations, then invoke <code>bv_decide</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold safeRefill saturatingAdd64 maxU64; bv_decide</code>
  </details>

- **Exercises 5–7 (`checkedBill` & `safeMidU64_in_bounds`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>bv_decide</code> understands fixed-width bitvectors and <code>UInt64</code> directly, but not <code>Option</code> constructors—eliminate <code>Option</code> first!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>checkedBill_sound</code>, <code>unfold checkedBill at hBill; split at hBill</code>. Close the <code>none</code> case with <code>nomatch hBill</code>, extract <code>total</code> with <code>injection hBill with hEq; subst hEq</code>, then call <code>bv_decide</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For Exercise 7: <code>unfold safeMidU64; bv_decide</code>.
  </details>

**Check your explanation**
> *Why does `(price ≤ balance) && (fee ≤ balance - price)` avoid wrap-around across all $2^{192}$ 64-bit inputs, and why would reversing the order of those two `&&` clauses reintroduce an underflow bug?*

---

### Chapter 11 — Pure Effects & Termination as DoS Defense (`ProveIt/Ch11.lean`)

**Socratic Warm-Up**
- Compare `StateT σ (Except ε) α` (`σ → Except ε (α × σ)`) against `ExceptT ε (StateM σ) α` (`σ → Except ε α × σ`). Which one rolls back state automatically when `throw` executes halfway through a transaction, and why?
- Why is a `termination_by` proof on a network/config parser a security control rather than pedantic math?

#### Progressive Hints (`Ch11.lean`)

- **Exercises 1 & 2 (`debitWithFee` & `debitWithFee_conserves`)**
  <details><summary>Hint 1 — Nudge</summary>
  Mirror <code>transferAliceToBob</code>: read <code>let v ← get</code>, guard <code>if v.balance &lt; amount + fee then throw ...</code>, then <code>set</code> the updated <code>Vault</code> and <code>return</code> the remaining balance.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold the <code>StateT</code>/<code>Except</code> monad operations at <code>hOk</code> with <code>simp only [...] at hOk</code>, <code>split at hOk</code> on the balance guard, discard the <code>throw</code> branch via <code>nomatch hOk</code>, and unpack <code>.ok (rem, v')</code> with <code>injection</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  After <code>subst hRem hState</code>, use <code>refine ⟨rfl, ?_⟩; simp only; omega</code>.
  </details>

- **Exercises 3, 4 & 5 (`resolveConfig_pos_fuel`, `resolveConfig_mono`, `lowerBound_in_range`)**
  <details><summary>Hint 1 — Nudge</summary>
  Never manually recreate the nested <code>if</code>/<code>match</code> tree of a recursive function—let <code>fun_induction</code> generate the exact branches and inductive hypotheses for you!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>resolveConfig_mono</code>, run <code>fun_induction resolveConfig env fuel key generalizing fuel'</code> so the inductive hypothesis holds for <code>f'</code> after <code>cases fuel'</code>! In <code>lowerBound_in_range</code>, run <code>fun_induction lowerBound pred lo hi</code> and feed <code>by omega</code> into each branch's <code>ih</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In <code>resolveConfig_mono</code>'s alias case: <code>cases fuel' with | zero =&gt; omega | succ f' =&gt; simp only [resolveConfig, hSome]; exact ih f' hOk (by omega)</code>.
  </details>

**Check your explanation**
> *Why did we pass `generalizing fuel'` to `fun_induction` in `resolveConfig_mono`, whereas `lowerBound_in_range` worked without `generalizing`?*

---

### Chapter 12 — Refinement Mappings & Stuttering Steps (`ProveIt/Ch12.lean`)

**Socratic Warm-Up**
- Why is proving an optimized engine against a 15-line `SpecKV` via `abs : ImplKV → SpecKV` drastically simpler than writing 20 standalone theorems (`put_then_get`, `put_then_delete_then_get`, `compact_then_get`, ...)?
- What does it mean for background log compaction to be a **stuttering step**, and why do LSM-trees need tombstones (`value := none`) instead of simply deleting keys from the newest layer?

#### Progressive Hints (`Ch12.lean`)

- **Exercises 1, 2 & 3 (`put_refines`, `delete_refines`, `put_preserves_invariant`)**
  <details><summary>Hint 1 — Nudge</summary>
  Use <code>apply SpecKV.ext; intro q</code> to reduce equality of abstract KV stores to pointwise lookup equality on an arbitrary query key <code>q</code>.
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Because <code>replayLog</code>, <code>lookupCache</code>, <code>ImplKV.put</code>, and <code>SpecKV.put</code> are marked <code>@[simp]</code>, <code>simp only [...]</code> reduces Exercises 1–2 immediately! For Exercise 3, case-split on <code>cases hEq : (q == k)</code> in both <code>hHit</code> and the goal.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  Exercise 3: <code>intro q res hHit; simp only [ImplKV.put, lookupCache] at hHit; simp only [ImplKV.put, replayLog]; cases hEq : (q == k) &lt;;&gt; simp [hEq] at hHit ⊢</code>, then finish with <code>exact hInv q res hHit</code> and <code>exact hHit</code>.
  </details>

- **Exercises 4, 5 & 6 (`compactLog_length_le`, `replayLog_compactLog`, `compact_stutters_and_consistent`)**
  <details><summary>Hint 1 — Nudge</summary>
  As <code>compactLog seen ops</code> walks from newest to oldest, <code>seen</code> accumulates keys whose newest value has already been emitted! Remember <code>induction ops generalizing seen</code> because the recursive call changes <code>seen</code> to <code>e.key :: seen</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>replayLog_compactLog</code>, split on <code>cases hKey : (k == e.key)</code>:
  - If <code>k == e.key</code> is <code>true</code>, then since <code>seen.contains k = false</code>, <code>compactLog</code> MUST keep <code>e</code> at the front!
  - If <code>k == e.key</code> is <code>false</code>, whether <code>e</code> is dropped or kept, <code>replayLog</code> skips <code>e</code> and <code>(e.key :: seen).contains k</code> remains <code>false</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  Instantiate <code>replayLog_compactLog [] s.log k rfl</code> inside <code>compact_stutters_and_consistent</code> after <code>apply SpecKV.ext; intro k</code>!
  </details>

**Check your explanation**
> *Suppose an engineer changes `ImplKV.delete` to remove `k` from `log` instead of prepending a `{ key := k, value := none }` tombstone (or suppose `compact` strips tombstones while an older SSTable still sits underneath). Which refinement theorem breaks, and what concrete bug hits production?*

---

### Checkpoint 3 (Closed-Notes) — Verified Fixed-Capacity Ring Buffer (`ProveIt/Checkpoints/Cp3.lean`)

**Socratic Warm-Up**
- Why did we replace `(head + offset) % cap` with `wrapAdd cap head offset` (`if head + offset < cap then head + offset else head + offset - cap`)? When is `wrapAdd` mathematically identical to `% cap`?
- Why doesn't `RingBuffer.pop` need to zero out or overwrite `rb.data[rb.head]` when dequeuing?

#### Progressive Hints (`Cp3.lean`)

- **Exercises 1 & 2 (`wrapAdd_lt`, `wrapAdd_inj`, `readSlice_length`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>omega</code> treats <code>if ... then ... else ...</code> as opaque until you split the condition!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold <code>wrapAdd</code> and run <code>split &lt;;&gt; omega</code> (or <code>split &lt;;&gt; split &lt;;&gt; omega</code> when two <code>wrapAdd</code> calls appear). For <code>readSlice_length</code>, induct on <code>len generalizing start</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>induction len generalizing start with | zero =&gt; rfl | succ n ih =&gt; simp only [readSlice, List.length_cons]; rw [ih (start + 1) (by omega)]</code>
  </details>

- **Exercises 3 & 4 (`RingBuffer.push` & `push_refines`)**
  <details><summary>Hint 1 — Nudge</summary>
  Use dependent <code>if hRoom : rb.count &lt; cap</code> so <code>wrapAdd_lt cap rb.head rb.count rb.hHead hRoom</code> proves the write index is strictly inside <code>rb.data</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>push_refines</code>, unfold <code>toQueue</code>, rewrite <code>readSlice ... (rb.count + 1)</code> with <code>readSlice_succ_snoc</code>, then rewrite the prefix with <code>readSlice_set_unreached</code> (showing the write at offset <code>rb.count</code> didn't touch offsets <code>0 .. rb.count - 1</code>) and simplify the tail read with <code>Array.getElem_set_self</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>rw [readSlice_succ_snoc]; simp only [Nat.zero_add]; rw [readSlice_set_unreached rb.data cap rb.hSize rb.head rb.hHead rb.count hRoom x _ 0 rb.count (by omega)]; simp only [Array.getElem_set_self]</code>
  </details>

- **Exercises 5 & 6 (`RingBuffer.pop` & `pop_refines`)**
  <details><summary>Hint 1 — Nudge</summary>
  Destructure <code>rcases rb with ⟨data, head, _ | c, hCap, hSize, hHead, hCount⟩</code> at the very start of <code>pop_refines</code> so <code>count</code> is concretely <code>0</code> or <code>c + 1</code> before unfolding dependent proof terms!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In the <code>c + 1</code> case, <code>readSlice ... head _ 0 (c + 1)</code> unfolds to <code>data[wrapAdd cap head 0] :: readSlice ... head _ 1 c</code>. Show <code>wrapAdd cap head 0 = head</code> and apply <code>readSlice_shift_head</code> symmetrically!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>congr 1; · congr 1; · exact (readSlice_shift_head data cap hSize head hHead _ 0 c (by omega)).symm</code>
  </details>

**Check your explanation**
> *Walk through why `push` followed by `pop` across the physical wrap-around boundary (`head = cap - 1`) preserves FIFO order without ever copying elements or clearing dequeued slots.*

---

## Part IV: Verification in the Age of AI Agents

### Chapter 13 — How AI Cheats Formal Verification (`ProveIt/Ch13.lean`)

**Socratic Warm-Up**
- An LLM agent submits `theorem withdraw_safe (s : State) (h : Valid s) : withdraw s amt = some s' → Conserved s s'` with zero `sorry` and clean `#print axioms`. Name **two completely different cheats** that could still make `withdraw` unusable or catastrophic in production!
- Why does `bal - amt ≤ bal` hold for *every* `bal, amt : Nat` in Lean, even when `bal = 5` and `amt = 1_000_000`?

#### Progressive Hints (`Ch13.lean`)

- **Exercises 1 & 2 (`badLimiterConfig_vacuous` & `goodLimiterConfig_nonvacuous`)**
  <details><summary>Hint 1 — Nudge</summary>
  Pull the three proof fields out of <code>cfg : BadLimiterConfig</code> (<code>cfg.hMinRate</code>, <code>cfg.hBurst</code>, <code>cfg.hCap</code>) and check what <code>2 * sustainedRate</code> implies for <code>burstLimit</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  <code>omega</code> proves <code>False</code> directly once those three field hypotheses are in scope! For Exercise 2, pick concrete numbers like <code>sustainedRate := 100</code>, <code>burstLimit := 250</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  Exercise 1: <code>have := cfg.hMinRate; have := cfg.hBurst; have := cfg.hCap; omega</code>. Exercise 2: <code>refine ⟨{ sustainedRate := 100, burstLimit := 250, hMinRate := by omega, hBurst := by omega, hCap := by omega }, by simp only; omega⟩</code>.
  </details>

- **Exercises 3, 4 & 5 (`naiveWithdraw_creates_money`, `checkedWithdraw`, Conservation & Non-Vacuity)**
  <details><summary>Hint 1 — Nudge</summary>
  Pick any <code>amt &gt; bal</code> (e.g., <code>bal := 20, amt := 100</code>) so <code>naiveWithdraw 20 100</code> truncates to <code>0</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Guard <code>checkedWithdraw</code> with <code>if amt ≤ bal then some (bal - amt) else none</code>. In <code>checkedWithdraw_conserves</code>, <code>split at hOk</code> gives <code>amt ≤ bal</code>, which lets <code>omega</code> prove <code>(bal - amt) + amt = bal</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For <code>checkedWithdraw_nonvacuous</code>: <code>refine ⟨100, 40, 60, by omega, rfl⟩</code>.
  </details>

**Check your explanation**
> *List the 4 mandatory gates in a formal-verification CI pipeline (`Spec` file permissions, `#print axioms`, exact postconditions vs `Nat` truncation, and non-vacuity/liveness witnesses) and state which specific LLM exploit each gate blocks.*

---

### Chapter 14 — Spec-First Agentic Co-Design (`ProveIt/Ch14.lean`)

**Socratic Warm-Up**
- Why should `namespace Spec` live in a read-only file/CODEOWNERS boundary that coding agents cannot edit during proof repair?
- Why did `split at hStep` inside `step_preserves_invariant` generate **6** proof obligations instead of the **20** cases produced by `cases s.phase <;> cases act`? What happens to both proofs next quarter when product adds a 6th `Action` constructor?

#### Progressive Hints (`Ch14.lean`)

- **Exercises 1 & 2 (`Impl.step` & `step_terminal_final`)**
  <details><summary>Hint 1 — Nudge</summary>
  Pattern-match on <code>match s.phase, act with</code>, handling the 5 valid transitions explicitly and ending with a catch-all <code>| _, _ =&gt; none</code>. Bind <code>let sp := splitPayout s.escrowLocked feeBps</code> and use <code>sp.1</code> / <code>sp.2</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>step_terminal_final</code>, destructure <code>rcases hTerm with hRel | hRef</code>, unfold <code>step</code>, and rewrite <code>rw [hRel]</code> (or <code>rw [hRef]</code>)—the catch-all arm reduces immediately!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>rcases hTerm with hRel | hRef &lt;;&gt; (unfold step; simp_all)</code> (or <code>· unfold step; rw [hRel]</code> and <code>· unfold step; rw [hRef]</code>).
  </details>

- **Exercises 3 & 4 (`step_preserves_invariant` & `impl_liveness_nonvacuous`)**
  <details><summary>Hint 1 — Nudge</summary>
  In the fee-bearing arms (<code>.release</code> and <code>.resolveToSeller</code>), call <code>have hSplit := splitPayout_spec s.escrowLocked _ hCap</code> so <code>omega</code> knows <code>sp.1 + sp.2 = s.escrowLocked</code> without fighting nonlinear division!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Unfold <code>step</code> at <code>hStep</code> and run <code>split at hStep</code>. In Arm 3 (<code>.funded</code> → <code>.disputed</code>), rewrite <code>ValidPhase</code> using <code>rw [‹s.phase = .funded›] at hPhase</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For Exercise 4, Lean can compute the concrete intermediate states automatically with holes <code>_</code> and <code>rfl</code> / <code>by decide</code>: <code>refine ⟨⟨_, _, rfl, rfl, by decide, by decide, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩</code>!
  </details>

**Check your explanation**
> *Explain why decomposing nonlinear arithmetic into a standalone helper lemma (`splitPayout_spec`) with `have` makes your top-level state-machine proof 5× faster and immune to changes in the fee rounding formula.*

---

### Chapter 15 — Verified Wire Formats (`ProveIt/Ch15.lean`)

**Socratic Warm-Up**
- Give an example of a buggy `encode`/`decode` pair that satisfies `∀ pkt, decode (encode pkt) = some pkt` yet breaks immediately when two packets arrive in a single `recv()` buffer on a TCP socket!
- How does `takeExact` prevent a TLS Heartbleed-style vulnerability when a malicious peer sends header `[tag = 0x03, len = 0xFFFF]` followed by only 4 bytes?

#### Progressive Hints (`Ch15.lean`)

- **Exercises 1, 2 & 3 (`decodeTag_encodeTag`, `takeExact_sound`, `takeExact_append`)**
  <details><summary>Hint 1 — Nudge</summary>
  <code>Tag</code> has only 4 constructors (<code>cases t &lt;;&gt; rfl</code>). For <code>takeExact_sound</code>, induct on <code>n generalizing xs chunk rem</code>; for <code>takeExact_append</code>, induct directly on <code>body</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In the <code>succ k</code> step of <code>takeExact_sound</code>, destructure <code>cases xs</code> (<code>nil</code> is impossible by <code>nomatch hTake</code>; on <code>cons x rest</code>, <code>split at hTake</code> on the recursive <code>takeExact k rest</code> call and apply <code>ih</code>).
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For <code>takeExact_append</code>: <code>induction body with | nil =&gt; rfl | cons b bs ih =&gt; simp only [List.length_cons, List.cons_append, takeExact, ih]</code>.
  </details>

- **Exercises 4 & 5 (`decodePacket_encodePacket_stream`, `decodeTwoPackets_stream`, `encodePacket_injective`)**
  <details><summary>Hint 1 — Nudge</summary>
  First reassociate <code>encodePacket pkt ++ rest</code> into <code>encodeTag pkt.tag :: (encodeU16BE pkt.body.length ++ (pkt.body ++ rest))</code> using <code>List.append_assoc</code> so <code>decodeU16BE_encodeU16BE</code> and <code>takeExact_append</code> fire in sequence!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Once <code>decodePacket_encodePacket_stream</code> is proved, <code>decodeTwoPackets_stream</code> is 3 lines (<code>rw [List.append_assoc]; unfold decodeTwoPackets; simp only [decodePacket_encodePacket_stream]</code>)! For injectivity, instantiate <code>decodePacket_encodePacket_stream</code> on <code>p1</code> and <code>p2</code> with <code>rest = []</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  In <code>encodePacket_injective</code>: <code>have h1 := decodePacket_encodePacket_stream p1 []; have h2 := decodePacket_encodePacket_stream p2 []; simp only [List.append_nil] at h1 h2; rw [hWire, h2] at h1; injection h1 with hPair; injection hPair with hPkt _; exact hPkt.symm</code>.
  </details>

**Check your explanation**
> *How did proving `decodePacket (encodePacket pkt ++ rest) = some (pkt, rest)` give us wire-format injectivity (`encodePacket p1 = encodePacket p2 → p1 = p2`) almost for free?*

---

### Chapter 16 — Monday-Morning Transfer (`ProveIt/Ch16.lean`)

**Socratic Warm-Up**
- Why must an idempotency-key gateway return `.conflict` (HTTP 422) when a client retries an existing `idempotencyKey` with a *different* `amount`, instead of blindly returning `.cached receiptId`?
- How does a 90-line Lean 4 differential oracle catch bugs in a 15,000-line Rust/Go/TypeScript microservice with PostgreSQL/Redis backing?

#### Progressive Hints (`Ch16.lean`)

- **Exercises 1, 2 & 3 (`idempotent_retry_stutters`, `idempotent_mismatch_conflicts`, `handlePayment_conserves`)**
  <details><summary>Hint 1 — Nudge</summary>
  Unfold <code>handlePayment</code> and rewrite with <code>hSeen : lookupKey s.records req.key = some rec</code>. For Exercise 2, convert <code>rec.amount ≠ req.amount</code> to <code>(rec.amount == req.amount) = false</code> via <code>beq_false_of_ne</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>handlePayment_conserves</code>, unfold <code>handlePayment</code> and <code>split</code> through the branches: 3 of the 4 outcomes return <code>s</code> untouched (<code>rfl</code>), and the fresh-charge branch has <code>req.amount ≤ s.customerBalance</code> so <code>omega</code> proves <code>(bal - amt) + (vol + amt) = bal + vol</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold handlePayment; split; · split &lt;;&gt; rfl; · split; · simp only; omega; · rfl</code>
  </details>

- **Exercises 4 & 5 (`runTrace_conserves`, `matchesOracle`, `matchesOracle_implies_conserved`)**
  <details><summary>Hint 1 — Nudge</summary>
  Induct on <code>reqs generalizing s</code> in <code>runTrace_conserves</code>! Why <code>generalizing s</code>? Because <code>runTrace</code> steps from <code>s</code> to <code>s1 := (handlePayment s req).2</code> on each request!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  Define <code>matchesOracle</code> with <code>runTrace s reqs == (obsResps, obsFinal)</code>. In <code>matchesOracle_implies_conserved</code>, turn <code>==</code> into <code>=</code> via <code>simp only [beq_iff_eq] at hPass</code> and rewrite <code>runTrace_conserves s reqs</code> with <code>hPass</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>unfold matchesOracle at hPass; simp only [beq_iff_eq] at hPass; have hCons := runTrace_conserves s reqs; rw [hPass] at hCons; exact hCons</code>
  </details>

**Check your explanation**
> *Sketch a 20-line integration test in your primary production language (Rust, Go, TypeScript, or Python) that replays JSON traces from `renderGoldenVector` (or pipes random property-test traces through `lean --run`) to verify your production idempotency middleware.*

---

### Checkpoint 4 (Closed-Notes) — Red-Team & Repair an AI-Verified Batch Escrow Module (`ProveIt/Checkpoints/Cp4.lean`)

**Socratic Warm-Up**
- Before writing a single tactic, read `BuggyAI` line by line and spot all **three** planted flaws:
  1. Which two conjuncts of `AiValidBatch` contradict each other?
  2. What happens inside `aiSettleOne 100 95 20`?
  3. Why did `AiConserved 100 0` evaluate to `True` even though funds didn't balance?

#### Progressive Hints (`Cp4.lean`)

- **Exercises 1 & 2 (Red-Team `BuggyAI`)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>AiValidBatch</code>, compare <code>pool &lt; reserveMin</code> against <code>sumList payouts + reserveMin ≤ pool</code>! For Exercise 2, choose <code>payout ≤ pool</code> where <code>payout + fee &gt; pool</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  <code>unfold AiValidBatch at h; omega</code> proves <code>False</code> for Flaw 1. For Exercise 2, try <code>pool := 100, payout := 95, fee := 20, newPool := 0</code>.
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  <code>refine ⟨100, 95, 20, 0, rfl, ?_, by omega⟩; unfold AiConserved; omega</code>
  </details>

- **Exercises 3, 4, 5 & 6 (`VerifiedRepair`: Implementation, Soundness & Non-Vacuity)**
  <details><summary>Hint 1 — Nudge</summary>
  In <code>settleOne</code>, guard on <code>s.reserveMin + payout + fee ≤ s.pool</code>—that single check simultaneously prevents <code>Nat</code> underflow AND preserves <code>ReserveSafe</code>!
  </details>
  <details><summary>Hint 2 — Strategy</summary>
  In <code>settleBatch_sound</code>, induct on <code>items generalizing s</code>, chaining step-by-step conservation with the provided <code>ExactConservation.refl</code> and <code>ExactConservation.trans</code>!
  </details>
  <details><summary>Hint 3 — Tactic Blueprint</summary>
  For Exercise 6 (<code>settleBatch_nonvacuous</code>), pick small concrete numbers like <code>pool := 100, reserveMin := 20</code> and <code>[(30, 2), (25, 1)]</code> so kernel reduction is instant: <code>refine ⟨s0, _, batch, by unfold ReserveSafe; decide, by decide, rfl, rfl, by decide, by decide⟩</code>.
  </details>

**Check your explanation**
> *Suppose a coworker proposes changing `settleBatch` so that if item #3 of 5 fails, items #1 and #2 stay settled and the function returns `(settledSoFar, failedRest)`. How would `settleBatch`'s type signature and `ExactConservation` contract need to change so callers cannot accidentally double-pay items #1 and #2 on retry?*
