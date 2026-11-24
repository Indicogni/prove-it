/-
  Chapter 16: Monday-Morning Transfer
  ===================================

  You do NOT have to rewrite your Rust, Go, TypeScript, or Python production
  codebase in Lean 4 to get real ROI on Monday morning.

  Follow the **Differential Oracle Playbook** (used by AWS Cedar & verified systems teams):
  1. Model the bug-prone core state machine in ~80 lines of Lean 4—here, a
     **Stripe-style Idempotency-Key Payment Gateway**.
  2. Prove the critical business invariants once and for all:
     - **Zero Double-Charge**: retrying the same `(key, amount)` replays the
       original receipt without deducting another cent.
     - **Payload-Mismatch Protection**: reusing an `idempotencyKey` with a
       *different* `amount` returns `.conflict` (HTTP 422) without mutating state.
     - **Trace-Wide Conservation**: total funds are conserved across arbitrary
       multi-request traces.
  3. Export deterministic JSON test vectors and a boolean **Differential Oracle**
     (`matchesOracle`) so CI fuzzers can check your Rust/Go/TS/Python service
     against mathematical ground truth on every pull request!
-/
set_option autoImplicit false

namespace ProveIt.Ch16

/-! ## 1. Idempotency-Key Payment Gateway Model -/

structure PaymentReq where
  key    : String
  amount : Nat
  deriving Repr, DecidableEq

structure IdemRecord where
  key       : String
  amount    : Nat
  receiptId : Nat
  deriving Repr, DecidableEq

inductive GatewayResp where
  | charged          (receiptId : Nat)
  | cached           (receiptId : Nat)
  | conflict
  | insufficientFunds
  deriving Repr, DecidableEq

structure GatewayState where
  customerBalance : Nat
  merchantVolume  : Nat
  nextReceiptId   : Nat
  records         : List IdemRecord
  deriving Repr, DecidableEq

@[simp]
def lookupKey : List IdemRecord → String → Option IdemRecord
  | [], _ => none
  | r :: rs, k => if r.key == k then some r else lookupKey rs k

/--
  Verified reference transition for an idempotent payment endpoint:
  - Seen key + matching `amount` → replay `.cached r.receiptId` (zero state change!)
  - Seen key + different `amount` → `.conflict` (zero state change!)
  - Fresh key + enough balance → debit customer, credit merchant, record receipt
  - Fresh key + insufficient balance → `.insufficientFunds` (leaves state unchanged)
-/
def handlePayment (s : GatewayState) (req : PaymentReq) : GatewayResp × GatewayState :=
  match lookupKey s.records req.key with
  | some rec =>
    if rec.amount == req.amount then
      (.cached rec.receiptId, s)
    else
      (.conflict, s)
  | none =>
    if req.amount ≤ s.customerBalance then
      let rid := s.nextReceiptId
      let newRec : IdemRecord := { key := req.key, amount := req.amount, receiptId := rid }
      (.charged rid, {
        customerBalance := s.customerBalance - req.amount
        merchantVolume  := s.merchantVolume + req.amount
        nextReceiptId   := rid + 1
        records         := newRec :: s.records
      })
    else
      (.insufficientFunds, s)

/-- Execute a sequence of payment requests, collecting all responses and final state. -/
def runTrace (s : GatewayState) : List PaymentReq → List GatewayResp × GatewayState
  | [] => ([], s)
  | req :: rest =>
    let (resp, s1) := handlePayment s req
    let (resps, sFinal) := runTrace s1 rest
    (resp :: resps, sFinal)

/-! ## 2. Exercises: Exact-Once Semantics, Conservation & Differential Oracle -/

/--
  EXERCISE 1 (Zero Double-Charge on Network Retry):
  Prove that if `req.key` was already processed with the SAME `amount`,
  `handlePayment` returns `.cached rec.receiptId` and leaves `s` 100% unchanged!
-/
theorem idempotent_retry_stutters (s : GatewayState) (req : PaymentReq) (rec : IdemRecord)
    (hSeen : lookupKey s.records req.key = some rec)
    (hSameAmt : rec.amount = req.amount) :
    handlePayment s req = (.cached rec.receiptId, s) := by
  sorry

/--
  EXERCISE 2 (Payload-Mismatch Conflict Protection):
  Prove that if `req.key` is reused with a DIFFERENT `amount`, `handlePayment`
  returns `.conflict` and leaves `s` 100% unchanged!
-/
theorem idempotent_mismatch_conflicts (s : GatewayState) (req : PaymentReq) (rec : IdemRecord)
    (hSeen : lookupKey s.records req.key = some rec)
    (hDiffAmt : rec.amount ≠ req.amount) :
    handlePayment s req = (.conflict, s) := by
  sorry

/--
  EXERCISE 3 (Single-Step Conservation of Funds):
  Prove that `customerBalance + merchantVolume` is invariant across ANY call
  to `handlePayment` (fresh charge, cached retry, conflict, or insufficient funds).
-/
theorem handlePayment_conserves (s : GatewayState) (req : PaymentReq) :
    let s' := (handlePayment s req).2
    s'.customerBalance + s'.merchantVolume = s.customerBalance + s.merchantVolume := by
  sorry

/--
  EXERCISE 4 (Multi-Step Trace Conservation):
  Lift `handlePayment_conserves` to arbitrary request traces `reqs : List PaymentReq`!
-/
theorem runTrace_conserves (s : GatewayState) (reqs : List PaymentReq) :
    let sFinal := (runTrace s reqs).2
    sFinal.customerBalance + sFinal.merchantVolume =
      s.customerBalance + s.merchantVolume := by
  sorry

/-! ## 3. Differential Oracle & JSON Test-Vector Export for Rust/Go/TS/Python -/

/--
  EXERCISE 5a: Implement the boolean differential-testing oracle `matchesOracle`.
  Given an initial `GatewayState`, an input trace `reqs`, and the `(obsResps, obsFinal)`
  captured from your production Rust/Go/TS/Python service, return `true` iff both
  the response list and final state match `runTrace s reqs`.
-/
def matchesOracle (s : GatewayState) (reqs : List PaymentReq)
    (obsResps : List GatewayResp) (obsFinal : GatewayState) : Bool :=
  let _ := (s, reqs, obsResps, obsFinal)
  sorry

/--
  EXERCISE 5b (Oracle Soundness Bridge):
  Prove that ANY external service trace passing `matchesOracle ... = true`
  is mathematically guaranteed to conserve funds!
-/
theorem matchesOracle_implies_conserved (s : GatewayState) (reqs : List PaymentReq)
    (obsResps : List GatewayResp) (obsFinal : GatewayState)
    (hPass : matchesOracle s reqs obsResps obsFinal = true) :
    obsFinal.customerBalance + obsFinal.merchantVolume =
      s.customerBalance + s.merchantVolume := by
  sorry

/-! ### Golden JSON Test-Vector Generator for CI Suites -/

def renderRespJson : GatewayResp → String
  | .charged rid   => s!"\{\"status\":\"charged\",\"receipt_id\":{rid}}"
  | .cached rid    => s!"\{\"status\":\"cached\",\"receipt_id\":{rid}}"
  | .conflict      => "{\"status\":\"conflict\"}"
  | .insufficientFunds => "{\"status\":\"insufficient_funds\"}"

def renderGoldenVector (initBal : Nat) (reqs : List PaymentReq) : String :=
  let s0 : GatewayState :=
    { customerBalance := initBal, merchantVolume := 0, nextReceiptId := 1, records := [] }
  let (resps, sf) := runTrace s0 reqs
  let respsStr := String.intercalate "," (resps.map renderRespJson)
  s!"\{\"init_balance\":{initBal},\"responses\":[{respsStr}],\"final_balance\":{sf.customerBalance},\"final_volume\":{sf.merchantVolume}}"

/--
info: "{\"init_balance\":500,\"responses\":[{\"status\":\"charged\",\"receipt_id\":1},{\"status\":\"cached\",\"receipt_id\":1},{\"status\":\"conflict\"},{\"status\":\"insufficient_funds\"}],\"final_balance\":200,\"final_volume\":300}"
-/
#guard_msgs in
#eval renderGoldenVector 500 [
  { key := "idem-1", amount := 300 }, -- 1. Fresh charge -> receipt 1
  { key := "idem-1", amount := 300 }, -- 2. Exact retry -> cached receipt 1 (no double charge!)
  { key := "idem-1", amount := 999 }, -- 3. Tampered amount -> conflict!
  { key := "idem-2", amount := 250 }  -- 4. Fresh key over remaining 200 -> insufficient_funds!
]

end ProveIt.Ch16
