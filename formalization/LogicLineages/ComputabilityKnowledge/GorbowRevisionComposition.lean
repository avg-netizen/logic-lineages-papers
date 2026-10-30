module

public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! The actual-instance semantic families underlying the published FS and UBF
figures. They are not yet the represented universally coded axiom sentences.
Atomic formulas retain every term constructor, including u; their substituting
closed terms are restricted to arithmetic. Quantified truth uses full closed-L
terms, while UBF uses closed arithmetic terms. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRevisionComposition
open GorbowSyntax

def AtomicMinus : {n : Nat} → Formula n → Prop
  | _, .equal _ _ => True
  | _, .universalRelation _ => True
  | _, .agent _ => True
  | _, _ => False

def AllContextVariables {n : Nat} (φ : Formula n) : Prop := ∀ i : Fin n, φ.uses i = true
end LogicLineages.ComputabilityKnowledge.GorbowRevisionComposition
