set_option autoImplicit false

/-!
# Checkpoint 1 (Closed-Notes): Zero-Panic Rollout & Canary Router (Reference Solutions)

This checkpoint synthesizes Part I (Chapters 1–4):
- Chapter 1: Avoiding `Nat` truncation and proving conservation laws (`omega`).
- Chapter 2: Modeling mutually exclusive lifecycle states (`inductive` / `structure`).
- Chapter 3: Compile-time exhaustion and Boolean Reflection (`↔`, `decide`).
- Chapter 4: Verifying state-machine transitions preserve safety invariants.
-/

namespace Cp1

/-!
## Part A: Domain Types & Total Traffic Splitting
-/

inductive RollbackReason where
  | manualAbort
  | budgetExceeded
  deriving Repr, DecidableEq

inductive RolloutPhase where
  | stable
  | canary (desiredPct : Nat) (errorCount : Nat)
  | promoted
  | rolledBack (reason : RollbackReason)
  deriving Repr, DecidableEq

structure TrafficSplit where
  stablePct : Nat
  canaryPct : Nat
  deriving Repr, DecidableEq

/--
Task 1.1: Implement `trafficSplit` without `Nat` truncation bugs:
- `.stable` routes `100%` to stable, `0%` to canary.
- `.promoted` routes `0%` to stable, `100%` to canary.
- `.rolledBack _` routes `100%` to stable, `0%` to canary.
- `.canary desiredPct errorCount`:
  - If `errorCount ≤ errorBudget`, clamp `c := if desiredPct ≤ 100 then desiredPct else 100`
    and route `(100 - c, c)`.
  - If `errorBudget < errorCount`, automatically shed canary traffic: `(100, 0)`.
-/
def trafficSplit (phase : RolloutPhase) (errorBudget : Nat) : TrafficSplit :=
  match phase with
  | .stable => { stablePct := 100, canaryPct := 0 }
  | .promoted => { stablePct := 0, canaryPct := 100 }
  | .rolledBack _ => { stablePct := 100, canaryPct := 0 }
  | .canary desiredPct errorCount =>
    if errorCount ≤ errorBudget then
      let c := if desiredPct ≤ 100 then desiredPct else 100
      { stablePct := 100 - c, canaryPct := c }
    else
      { stablePct := 100, canaryPct := 0 }

#guard trafficSplit (.canary 25 2) 5 == { stablePct := 75, canaryPct := 25 }
#guard trafficSplit (.canary 150 2) 5 == { stablePct := 0, canaryPct := 100 }
#guard trafficSplit (.canary 25 6) 5 == { stablePct := 100, canaryPct := 0 }
#guard trafficSplit (.rolledBack .budgetExceeded) 5 == { stablePct := 100, canaryPct := 0 }

/--
Task 1.2: Prove that `stablePct + canaryPct = 100` across *every* `RolloutPhase`
and *every* `errorBudget` (including `desiredPct > 100`).
-/
theorem trafficSplit_sums_to_100 (phase : RolloutPhase) (errorBudget : Nat) :
    (trafficSplit phase errorBudget).stablePct +
    (trafficSplit phase errorBudget).canaryPct = 100 := by
  cases phase with
  | stable => rfl
  | promoted => rfl
  | rolledBack _ => rfl
  | canary desiredPct errorCount =>
    dsimp [trafficSplit]
    split
    · dsimp
      split <;> omega
    · rfl

/--
Task 1.3: Prove that an unhealthy canary (`errorBudget < errorCount`) receives
`0%` traffic regardless of `desiredPct`.
-/
theorem unhealthy_canary_sheds_traffic
    (desiredPct errorCount errorBudget : Nat)
    (hUnhealthy : errorBudget < errorCount) :
    (trafficSplit (.canary desiredPct errorCount) errorBudget).canaryPct = 0 := by
  dsimp [trafficSplit]
  split
  · omega
  · rfl

/-!
## Part B: Promotion Gate & Boolean Reflection
-/

inductive Env where
  | staging
  | prod
  deriving Repr, DecidableEq

inductive Approval where
  | ciGreen
  | sreSignoff
  | breakGlass
  deriving Repr, DecidableEq

inductive CanPromote : Env → Approval → Prop where
  | stagingAny (a : Approval) : CanPromote .staging a
  | prodSre                   : CanPromote .prod .sreSignoff
  | prodBreakGlass            : CanPromote .prod .breakGlass

/--
Task 1.4: Implement `checkPromote` to match `CanPromote` and prove Boolean Reflection.
-/
def checkPromote (env : Env) (approval : Approval) : Bool :=
  match env, approval with
  | .staging, _           => true
  | .prod,    .sreSignoff => true
  | .prod,    .breakGlass => true
  | .prod,    .ciGreen    => false

#guard checkPromote .prod .ciGreen == false
#guard checkPromote .prod .sreSignoff == true
#guard checkPromote .staging .ciGreen == true

theorem checkPromote_iff_canPromote (env : Env) (approval : Approval) :
    checkPromote env approval = true ↔ CanPromote env approval := by
  constructor
  · intro h
    match env, approval, h with
    | .staging, a,           _ => exact .stagingAny a
    | .prod,    .sreSignoff, _ => exact .prodSre
    | .prod,    .breakGlass, _ => exact .prodBreakGlass
  · intro h
    cases h with
    | stagingAny => cases approval <;> rfl
    | prodSre => rfl
    | prodBreakGlass => rfl

/-!
## Part C: Rollout Controller State Machine
-/

inductive RolloutEvent where
  | startCanary (pct : Nat)
  | recordError
  | promote (env : Env) (approval : Approval)
  | abort
  deriving Repr, DecidableEq

def stepRollout (phase : RolloutPhase) (ev : RolloutEvent) (errorBudget : Nat) :
    RolloutPhase :=
  match phase, ev with
  | .stable, .startCanary pct => .canary pct 0
  | .canary pct errs, .recordError =>
    if errs + 1 ≤ errorBudget then
      .canary pct (errs + 1)
    else
      .rolledBack .budgetExceeded
  | .canary _ errs, .promote env app =>
    if errs ≤ errorBudget && checkPromote env app then
      .promoted
    else
      phase
  | _, .abort => .rolledBack .manualAbort
  | _, _ => phase

def PhaseHealthy (phase : RolloutPhase) (errorBudget : Nat) : Prop :=
  match phase with
  | .canary _ errs => errs ≤ errorBudget
  | _              => True

/--
Task 1.5: Prove that `stepRollout` preserves `PhaseHealthy`: starting from any
healthy rollout phase, no single `RolloutEvent` can ever leave the controller in
an unhealthy `.canary` state (`errorBudget < errs`).
-/
theorem stepRollout_preserves_healthy
    (phase : RolloutPhase) (ev : RolloutEvent) (errorBudget : Nat)
    (hHealthy : PhaseHealthy phase errorBudget) :
    PhaseHealthy (stepRollout phase ev errorBudget) errorBudget := by
  match phase, ev with
  | .stable, .startCanary _ =>
    dsimp [stepRollout, PhaseHealthy]
    omega
  | .stable, .recordError => trivial
  | .stable, .promote _ _ => trivial
  | .stable, .abort => trivial
  | .canary _ _, .startCanary _ => exact hHealthy
  | .canary _ errs, .recordError =>
    dsimp [stepRollout]
    split
    · dsimp [PhaseHealthy]
      omega
    · trivial
  | .canary _ _, .promote _ _ =>
    dsimp [stepRollout]
    split
    · trivial
    · exact hHealthy
  | .canary _ _, .abort => trivial
  | .promoted, .startCanary _ => trivial
  | .promoted, .recordError => trivial
  | .promoted, .promote _ _ => trivial
  | .promoted, .abort => trivial
  | .rolledBack _, .startCanary _ => trivial
  | .rolledBack _, .recordError => trivial
  | .rolledBack _, .promote _ _ => trivial
  | .rolledBack _, .abort => trivial

/-- info: 'Cp1.trafficSplit_sums_to_100' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trafficSplit_sums_to_100

/-- info: 'Cp1.stepRollout_preserves_healthy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepRollout_preserves_healthy

end Cp1
