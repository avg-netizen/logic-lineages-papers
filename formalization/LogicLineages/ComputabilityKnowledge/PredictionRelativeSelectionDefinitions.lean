module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListDefinitions
public import Mathlib.Computability.RecursiveIn

@[expose] public section
/-! Actual relative selection for paper14 lem:list. These are exactly the
characteristic oracles of the named ordinary-program predicates, not an
assumed selection oracle. No identification with 0'' is asserted here. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionRelativeSelection
open PredictionCanonicalList

noncomputable def totalIndicator (i : Nat) : Nat := by
  classical exact if TotalNat (codeAt i) then 1 else 0

noncomputable def equalityIndicator (q : Nat) : Nat := by
  classical exact if SameFunction (codeAt q.unpair.1) (codeAt q.unpair.2) then 1 else 0

noncomputable def selectionOracles : Set (Nat → Part Nat) :=
  {fun n => Part.some (totalIndicator n), fun n => Part.some (equalityIndicator n)}

noncomputable def representativeIndicator (i : Nat) : Nat := by
  classical exact if Representative i then 1 else 0

noncomputable def representativeCount (n : Nat) : Nat := by
  classical exact Nat.count Representative n

end LogicLineages.ComputabilityKnowledge.PredictionRelativeSelection
