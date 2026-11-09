module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueTargets
open BlockRows PlainMaximum PlainMaximumResidue

def ActualOriginalTailCalibration : Prop := ∀ (m i : Nat) (r : Row) (ν : Nat → Nat),
  PlainMaximumResidue.cutoff m ≤ ν i →
    ((lowerAtom m i r).eval ν ↔ (Atom.divisible m r).eval ν)

def LiteralRemainingOccurrences : Prop := ∀ (m i : Nat) (r : Row),
  (lowerRow m i r).2 = r.2.filter (fun a => !isHead i a.2)

def ExactEliminandLinearity : Prop := ∀ (bound : List Nat) (r : Row) (m i : Nat),
  allowed bound r = true → i ∉ r.parameters → linearIn i (lowerAtom m i r) = true

def WholeBlockParameterPreservation : Prop :=
  ∀ (bound : List Nat) (r : Row) (m i : Nat),
    (∀ j ∈ bound, j ∉ r.parameters) → ParametersIndependent bound (lowerAtom m i r)

def OriginalNameSupport : Prop := ∀ (m i : Nat) (r : Row) (j : Nat),
  j ∈ (lowerAtom m i r).variables → j ∈ r.variables

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueTargets
