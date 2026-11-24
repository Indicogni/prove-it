set_option autoImplicit false

/-!
# Chapter 5: Proofs Are Programs, Goals Are Stack Traces (Reference Solutions)

When you open Lean's Infoview on a tactic block, you are looking at a **compile-time
stack frame**:
- Everything above `⊢` is a local variable or hypothesis already in scope.
- The expression after `⊢` is the return type your proof script still owes the
  type-checker.

Under the Curry-Howard correspondence, logical connectives *are* data types, and
tactics are structured code generators that assemble terms of those types.
-/

namespace Ch05

/-!
## 1. Implication (`→`) Is a Function Type

Compare a regular program `pipeTerm` with the tactic proof `pipeTactic` below:
both construct the exact same kernel function term!
-/

theorem pipeTerm (SigOk Fresh Enqueued : Prop)
    (step1 : SigOk → Fresh) (step2 : Fresh → Enqueued) (hSig : SigOk) :
    Enqueued :=
  step2 (step1 hSig)

theorem pipeTactic (SigOk Fresh Enqueued : Prop)
    (step1 : SigOk → Fresh) (step2 : Fresh → Enqueued) :
    SigOk → Enqueued := by
  intro hSig
  apply step2
  apply step1
  exact hSig

/-!
## 2. Modeling a Payment Webhook Ingress Contract
-/

structure WebhookReq where
  deliveryId  : Nat
  signatureOk : Bool
  ageSeconds  : Nat
  deriving Repr, DecidableEq

def SigValid (req : WebhookReq) : Prop :=
  req.signatureOk = true

def TimestampFresh (req : WebhookReq) : Prop :=
  req.ageSeconds ≤ 300

def ReplayExpired (req : WebhookReq) : Prop :=
  300 < req.ageSeconds

#guard decide (WebhookReq.mk 101 true 45).signatureOk == true

/-!
## 3. Conjunction (`∧`), Disjunction (`∨`), Negation (`¬`), `∀`, and `∃`

- `P ∧ Q`: a pair of proofs. Build with `constructor` (or `⟨hp, hq⟩`); unpack
  with `rcases h with ⟨hp, hq⟩`.
- `P ∨ Q`: a tagged union (`Or.inl` or `Or.inr`). Pick a side with `left` or
  `right`; branch on an existing `h : P ∨ Q` with `rcases h with hp | hq` or `cases h`.
- `¬ P`: shorthand for `P → False`. Introduce `P` with `intro hp` and derive `False`.
- `∀ x, P x`: a dependent function taking `x` and returning a proof of `P x`.
- `∃ x, P x`: a dependent pair `⟨witness, proofOfPWitness⟩`.
-/

theorem fresh_and_valid_swap (req : WebhookReq)
    (h : SigValid req ∧ TimestampFresh req) :
    TimestampFresh req ∧ SigValid req := by
  rcases h with ⟨hSig, hFresh⟩
  constructor
  · exact hFresh
  · exact hSig

theorem replay_window_partition (req : WebhookReq) :
    TimestampFresh req ∨ ReplayExpired req := by
  unfold TimestampFresh ReplayExpired
  omega

/-!
## Exercises (Solved)
-/

/--
Exercise 5.1 (`→` and `∧`):
Given a gateway rule `hGate` requiring bundled evidence `SigValid req ∧ TimestampFresh req`,
prove the curried API contract `SigValid req → TimestampFresh req → EnqueueJob req`.
-/
theorem uncurry_webhook_gate {EnqueueJob : WebhookReq → Prop} (req : WebhookReq)
    (hGate : SigValid req ∧ TimestampFresh req → EnqueueJob req) :
    SigValid req → TimestampFresh req → EnqueueJob req := by
  intro hSig hFresh
  apply hGate
  constructor
  · exact hSig
  · exact hFresh

/--
Exercise 5.2 (`∨` case analysis):
An idempotent webhook handler returns HTTP 200 OK whether a valid delivery was
already processed (`AlreadySeen req`) or newly enqueued (`EnqueueJob req`).
Prove `Return200 req` from `AlreadySeen req ∨ EnqueueJob req`.
-/
theorem idempotent_ack {AlreadySeen EnqueueJob Return200 : WebhookReq → Prop}
    (req : WebhookReq)
    (hOutcome : AlreadySeen req ∨ EnqueueJob req)
    (hCached : AlreadySeen req → Return200 req)
    (hEnqueued : EnqueueJob req → Return200 req) :
    Return200 req := by
  rcases hOutcome with hSeen | hJob
  · exact hCached hSeen
  · exact hEnqueued hJob

/--
Exercise 5.3a (`¬` as `→ False` / Contrapositive):
If every enqueued webhook must have a fresh timestamp, prove that a webhook
failing `TimestampFresh` can never be enqueued (`¬ EnqueueJob req`).
-/
theorem stale_webhook_rejected {EnqueueJob : WebhookReq → Prop} (req : WebhookReq)
    (hMustBeFresh : EnqueueJob req → TimestampFresh req)
    (hNotFresh : ¬ TimestampFresh req) :
    ¬ EnqueueJob req := by
  intro hEnq
  apply hNotFresh
  exact hMustBeFresh hEnq

/--
Exercise 5.3b (Mutual Exclusion of Concrete Predicates):
Prove that no `WebhookReq` can simultaneously satisfy `TimestampFresh` and
`ReplayExpired`.
-/
theorem fresh_and_expired_disjoint (req : WebhookReq) :
    ¬ (TimestampFresh req ∧ ReplayExpired req) := by
  intro hBoth
  rcases hBoth with ⟨hFresh, hExpired⟩
  unfold TimestampFresh at hFresh
  unfold ReplayExpired at hExpired
  omega

/--
Exercise 5.4 (`∀` specialization and `∃` witness forwarding):
Suppose:
- Every request with valid signature and fresh timestamp is enqueued (`hGate`), and
- Every enqueued request produces an audit log receipt with a non-zero `receiptId` (`hAudit`).
Prove that a valid, fresh request `req` produces some `receiptId` with `0 < receiptId`.
-/
theorem webhook_audit_witness
    {EnqueueJob : WebhookReq → Prop}
    {AuditLogged : WebhookReq → Nat → Prop}
    (hGate : ∀ r : WebhookReq, SigValid r ∧ TimestampFresh r → EnqueueJob r)
    (hAudit : ∀ r : WebhookReq, EnqueueJob r → ∃ receiptId : Nat, 0 < receiptId ∧ AuditLogged r receiptId)
    (req : WebhookReq)
    (hSig : SigValid req)
    (hFresh : TimestampFresh req) :
    ∃ receiptId : Nat, 0 < receiptId ∧ AuditLogged req receiptId := by
  have hEnq : EnqueueJob req := hGate req ⟨hSig, hFresh⟩
  rcases hAudit req hEnq with ⟨receiptId, hPos, hLogged⟩
  exact ⟨receiptId, hPos, hLogged⟩

/-- info: 'Ch05.webhook_audit_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms webhook_audit_witness

end Ch05
