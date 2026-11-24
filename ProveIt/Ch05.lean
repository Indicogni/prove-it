set_option autoImplicit false

/-!
# Chapter 5: Proofs Are Programs, Goals Are Stack Traces

Open Lean's Infoview and click through `pipeTactic` below. Read the Infoview
exactly like a debugger stack frame:
- Lines above `⊢` are local parameters and bindings already in scope.
- The line after `⊢` is the return type your code still owes the caller.

In Lean's type theory, **a proposition is a type, and a proof is a total program
producing a value of that type**.
-/

namespace Ch05

/-!
## 1. Implication (`→`) Is Function Composition

Compare `pipeTerm` (written as an ordinary expression) with `pipeTactic`
(written interactively with `intro`, `apply`, and `exact`):
-/

theorem pipeTerm (SigOk Fresh Enqueued : Prop)
    (step1 : SigOk → Fresh) (step2 : Fresh → Enqueued) (hSig : SigOk) :
    Enqueued :=
  step2 (step1 hSig)

-- PREDICT: Place your cursor after `apply step2`. What changes below `⊢`?
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
## 3. Tactic Reference Card: Connectives as Data Structures

| Connective | Software Analogy          | To Build (`⊢ ...`)       | To Unpack (`h : ...`)        |
|------------|---------------------------|--------------------------|------------------------------|
| `P → Q`    | Function `P -> Q`         | `intro hP`               | `apply h` or `have q := h p` |
| `P ∧ Q`    | Struct / Pair `(P, Q)`    | `constructor`            | `rcases h with ⟨hP, hQ⟩`     |
| `P ∨ Q`    | Sum / Enum `Left \| Right`| `left` or `right`        | `rcases h with hP \| hQ`     |
| `¬ P`      | `P → False`               | `intro hP` (prove False) | `apply hNotP`                |
| `∀ x, P x` | Generic / Dependent fn    | `intro x`                | `have hx := h x`             |
| `∃ x, P x` | Witness pair `⟨x, hx⟩`    | `refine ⟨w, ?_⟩`         | `rcases h with ⟨x, hx⟩`      |
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
## Exercises
-/

/--
Exercise 5.1 (`→` and `∧`):
Given a gateway rule `hGate` requiring a bundled pair `SigValid req ∧ TimestampFresh req`,
prove the curried contract `SigValid req → TimestampFresh req → EnqueueJob req`.
-/
theorem uncurry_webhook_gate {EnqueueJob : WebhookReq → Prop} (req : WebhookReq)
    (hGate : SigValid req ∧ TimestampFresh req → EnqueueJob req) :
    SigValid req → TimestampFresh req → EnqueueJob req := by
  sorry

/--
Exercise 5.2 (`∨` case analysis):
An idempotent webhook endpoint returns HTTP 200 OK whether a delivery was
already processed (`AlreadySeen req`) or newly enqueued (`EnqueueJob req`).
Prove `Return200 req` from `AlreadySeen req ∨ EnqueueJob req`.
-/
theorem idempotent_ack {AlreadySeen EnqueueJob Return200 : WebhookReq → Prop}
    (req : WebhookReq)
    (hOutcome : AlreadySeen req ∨ EnqueueJob req)
    (hCached : AlreadySeen req → Return200 req)
    (hEnqueued : EnqueueJob req → Return200 req) :
    Return200 req := by
  sorry

/--
Exercise 5.3a (`¬` as `→ False` / Contrapositive):
If every enqueued webhook must have a fresh timestamp (`hMustBeFresh`), prove
that a webhook failing `TimestampFresh` is never enqueued (`¬ EnqueueJob req`).
-/
theorem stale_webhook_rejected {EnqueueJob : WebhookReq → Prop} (req : WebhookReq)
    (hMustBeFresh : EnqueueJob req → TimestampFresh req)
    (hNotFresh : ¬ TimestampFresh req) :
    ¬ EnqueueJob req := by
  sorry

/--
Exercise 5.3b (Disjoint Time Windows):
Prove that no `WebhookReq` can simultaneously satisfy `TimestampFresh` and
`ReplayExpired`.
-/
theorem fresh_and_expired_disjoint (req : WebhookReq) :
    ¬ (TimestampFresh req ∧ ReplayExpired req) := by
  sorry

/--
Exercise 5.4 (`∀` specialization and `∃` witness forwarding):
Combine `hGate` and `hAudit` to construct an existential audit receipt witness
for a verified, fresh request `req`.
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
  sorry

end Ch05
