module

public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupport
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-! Structural free-occurrence transport for the unchanged capture-avoiding
substitution. The image is a literal finite union of replacement-term supports;
no semantic occurrence or truth predicate is substituted for actual syntax. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupport
open GorbowSyntax GorbowFreeSupport

def supportImage {m n : Nat} (σ : Fin m → Term n) (s : Finset Nat) : Finset Nat :=
  Finset.univ.biUnion (fun i : Fin m => if i.val ∈ s then termSupport (σ i) else ∅)
end LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupport
