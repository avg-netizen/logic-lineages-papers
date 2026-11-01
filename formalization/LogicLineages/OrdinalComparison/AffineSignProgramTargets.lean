module
public import LogicLineages.OrdinalComparison.AffineSignProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def AffineSourceSignProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat => encodedAffineSourceSign p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  ∀ a b c d : Nat, let result := encodedAffineSourceSign a b c d
    result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat, result.2≤x →
      (result.1=0 ↔ a*x+b<c*x+d) ∧ (result.1=1 ↔ a*x+b=c*x+d) ∧ (result.1=2 ↔ c*x+d<a*x+b)

/-- Exact terminal rule on literal actual P1 source trees, not an affine
semantic model supplied by a premise. -/
def ActualAffinePositiveSourceSigns : Prop :=
  ∀ a b c d : Nat, let result := encodedAffineSourceSign a b c d
    result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat, result.2≤x →
      (result.1=0 ↔ actualFixedLimitProfileEval (positiveAffineProfile a b) x<
        actualFixedLimitProfileEval (positiveAffineProfile c d) x) ∧
      (result.1=1 ↔ actualFixedLimitProfileEval (positiveAffineProfile a b) x=
        actualFixedLimitProfileEval (positiveAffineProfile c d) x) ∧
      (result.1=2 ↔ actualFixedLimitProfileEval (positiveAffineProfile c d) x<
        actualFixedLimitProfileEval (positiveAffineProfile a b) x)

/-- Exact same rule on the actual normalized collected source data used by
P/P comparison. Constants and input coefficients are kept in source order. -/
def ActualAffineCollectedSourceSigns : Prop :=
  ∀ a b c d : Nat, let result := encodedAffineSourceSign a b c d
    result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat, result.2≤x →
      (result.1=0 ↔ actualCollectedPositiveEval (.mk b a .nil) x<actualCollectedPositiveEval (.mk d c .nil) x) ∧
      (result.1=1 ↔ actualCollectedPositiveEval (.mk b a .nil) x=actualCollectedPositiveEval (.mk d c .nil) x) ∧
      (result.1=2 ↔ actualCollectedPositiveEval (.mk d c .nil) x<actualCollectedPositiveEval (.mk b a .nil) x)

end LogicLineages.OrdinalComparison.Targets
