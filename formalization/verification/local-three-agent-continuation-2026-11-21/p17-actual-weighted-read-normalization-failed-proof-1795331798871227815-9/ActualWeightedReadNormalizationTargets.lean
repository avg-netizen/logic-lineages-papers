module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
public import LogicLineages.PermittedControl.InnerTerminationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualWeightedReadNormalization
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement

/-- Combine literally identical original operand keys, with their
signed weights. Zero weights vanish from the finite support. -/
noncomputable def groupedWeights : List Read → LowerOperand →₀ Int
  | [] => 0
  | r::rs => Finsupp.single r.1.2 r.1.1 + groupedWeights rs

noncomputable def weightAt (op : LowerOperand) (r : Read) : Int := by
  classical
  exact if r.1.2 = op then r.1.1 else 0

/-- Check every supplied real read before inspecting the grouped support.
Even a zero weight or a pair summing to zero must pass the original read. -/
noncomputable def checkedReads (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read) : Bool :=
  xs.all fun r => decide (lowerOperandRead f ρ r.1.2 = some (some r.2))

noncomputable def readAtWeight (f : Nat → Nat) (ρ : Nat → Nat)
    (weights : LowerOperand →₀ Int) (op : LowerOperand) : Option Read :=
  (lowerOperandRead f ρ op).join.map (fun v => ((weights op,op),v))

noncomputable def normalizeReads (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read) :
    Option (List Read) :=
  if checkedReads f ρ xs then
    let weights := groupedWeights xs
    weights.support.toList.mapM (readAtWeight f ρ weights)
  else none

def ExactGroupedWeights : Prop :=
  ∀ (xs : List Read) (op : LowerOperand),
    groupedWeights xs op = (xs.map (weightAt op)).sum ∧
    (op ∈ (groupedWeights xs).support ↔ (xs.map (weightAt op)).sum ≠ 0) ∧
    (op ∈ (groupedWeights xs).support → ∃ r ∈ xs, r.1.2 = op)

def ExactInputChecks : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read),
    checkedReads f ρ xs = true ↔ liftedReads f ρ xs

def ExactNormalizedReads : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (xs : List Read),
    (normalizeReads f ρ xs = none ↔ ¬ liftedReads f ρ xs) ∧
    (liftedReads f ρ xs → ∃ ys : List Read,
      normalizeReads f ρ xs = some ys ∧
      ys.map (fun r => r.1.2) = (groupedWeights xs).support.toList ∧
      (ys.map (fun r => r.1.2)).Nodup ∧
      liftedReads f ρ ys ∧ readSum xs = readSum ys ∧
      ∀ r ∈ ys, r.1.1 = groupedWeights xs r.1.2 ∧ r.1.1 ≠ 0 ∧
        ∃ prior ∈ xs, prior.1.2 = r.1.2 ∧ prior.2 = r.2)

def FullActualWeightedReadNormalization : Prop :=
  ExactGroupedWeights ∧ ExactInputChecks ∧ ExactNormalizedReads

end LogicLineages.PermittedControl.ActualWeightedReadNormalization
