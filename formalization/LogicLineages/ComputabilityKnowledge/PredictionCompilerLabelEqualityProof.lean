module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityProof
open Turing Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport
open PredictionCompilerLabelEquality PredictionCompilerLabelEqualityTargets

private theorem symbols_all (s : Store) : s ∈ symbols := by
  cases s with | none => simp [symbols] | some a => cases a <;> simp [symbols]

theorem exactStoreComparison : ExactStoreComparison := by
  intro β _ f g
  constructor
  · intro h
    funext s
    exact of_decide_eq_true ((List.all_eq_true.mp h) s (symbols_all s))
  · rintro rfl
    simp [sameStore]

private theorem store_iff {β : Type} [DecidableEq β] (f g : Store → β) :
    sameStore f g = true ↔ f = g := exactStoreComparison β f g

theorem exactDoubleStoreComparison : ExactDoubleStoreComparison := by
  intro β _ f g
  constructor
  · intro h
    funext s
    exact (store_iff (f s) (g s)).1 ((List.all_eq_true.mp h) s (symbols_all s))
  · rintro rfl
    simp [sameStore₂, store_iff]

private theorem double_iff {β : Type} [DecidableEq β] (f g : Store → Store → β) :
    sameStore₂ f g = true ↔ f = g := exactDoubleStoreComparison β f g

theorem exactStackStatementComparison : ExactStackStatementComparison := by
  intro q
  induction q <;> intro r <;> cases r <;>
    simp_all [stackEq, store_iff, double_iff, and_assoc]

private theorem stack_iff (q r : StackStatement) : stackEq q r = true ↔ q = r :=
  exactStackStatementComparison q r

theorem exactStackActionComparison : ExactStackActionComparison := by
  intro k a b
  cases a <;> cases b <;> simp [actionEq, store_iff, double_iff]

private theorem action_iff {k : K'} (a b : TM2to1.StAct K' StackAlphabet Store k) :
    actionEq a b = true ↔ a = b := exactStackActionComparison k a b

theorem exactTapeLabelComparison : ExactTapeLabelComparison := by
  intro q r
  cases q with
  | normal l => cases r <;> simp [labelEq]
  | ret q => cases r <;> simp [labelEq, stack_iff]
  | go k a q =>
    cases r with
    | normal l => simp [labelEq]
    | ret r => simp [labelEq]
    | go j b r =>
      by_cases h : k = j
      · subst j
        simp [labelEq, action_iff, stack_iff]
      · simp [labelEq, h]

/-- The instance is computed by the checked finite Boolean test. -/
def stackDecidableEq : DecidableEq StackStatement := fun q r =>
  decidable_of_iff (stackEq q r = true) (exactStackStatementComparison q r)

/-- No classical equality is used by this decision procedure. -/
def labelDecidableEq : DecidableEq TapeLabel := fun q r =>
  decidable_of_iff (labelEq q r = true) (exactTapeLabelComparison q r)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityProof
