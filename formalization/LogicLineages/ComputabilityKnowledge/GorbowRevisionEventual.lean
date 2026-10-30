module

public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

@[expose] public section

/-! Quantitative external eventual validity in the actual one-agent revision
sequence. This pays rule preservation, not the missing source DCB axioms or
represented universally coded source apparatus, and is not KT consistency. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRevisionEventual
open GorbowSyntax GorbowCodeConstructors GorbowRevisionSemantics

def Threshold (g : Ground) (initial : Extension) (σ : Sentence) (N : Nat) : Prop :=
  ∀ n, N ≤ n → σ.realize (stage g initial n) Fin.elim0

def Eventually (g : Ground) (initial : Extension) (σ : Sentence) : Prop :=
  ∃ N, Threshold g initial σ N

def allAgentsKnow (σ : Sentence) : Sentence :=
  .all (.imp (.agent (.var 0)) (.knowledge (.var 0) (Term.numeral (formulaNumber σ))))
end LogicLineages.ComputabilityKnowledge.GorbowRevisionEventual
