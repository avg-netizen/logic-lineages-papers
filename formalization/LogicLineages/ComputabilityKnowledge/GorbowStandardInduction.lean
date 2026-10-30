module

public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! The actual full-language induction formula in a standard-N expansion.
Index0 is the induction variable; old context positions are preserved.
Universal closure binds the newest remaining parameter at each step.
This specifies the PA(L) schema, not a DCB/KT proof relation or consistency. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowStandardInduction

open GorbowSyntax GorbowStandardInstances

def successorInstance {n : Nat} (φ : Formula (n + 1)) : Formula (n + 1) :=
  GorbowFormulaSubstitution.substituteFormula
    (Fin.cases (.succ (.var 0)) (fun i : Fin n => .var i.succ)) φ

def inductionAxiom {n : Nat} (φ : Formula (n + 1)) : Formula n :=
  .imp (instantiate φ .zero) (.imp (.all (.imp φ (successorInstance φ))) (.all φ))

def universalClosure : {n : Nat} → Formula n → Sentence
  | 0, φ => φ
  | n + 1, φ => universalClosure (n := n) (.all φ)

def closedInductionAxiom {n : Nat} (φ : Formula (n + 1)) : Sentence :=
  universalClosure (inductionAxiom φ)

end LogicLineages.ComputabilityKnowledge.GorbowStandardInduction
