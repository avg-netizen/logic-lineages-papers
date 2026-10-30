module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBinding
public import LogicLineages.ComputabilityKnowledge.GorbowContextTransport

@[expose] public section

/-! Actual closed named instances. Zero-filling other source variables is
identified with source [t/v] only when v is the unique free name, never as a
replacement for arbitrary open substitution. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition
open GorbowSyntax

def namedClosedDictionary {n : Nat} (v : Fin n) (t : Term 0) : Fin n → Term 0 :=
  fun i => if i=v then t else .zero
def namedClosedInstance {n : Nat} (v : Fin n) (φ : Formula n) (t : Term 0) : Sentence :=
  GorbowFormulaSubstitution.substituteFormula (namedClosedDictionary v t) φ
end LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition
