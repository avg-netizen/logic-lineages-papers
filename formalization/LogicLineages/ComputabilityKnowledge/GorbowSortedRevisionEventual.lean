module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevision

@[expose] public section

/-! Quantitative external eventual validity in the fresh sorted one-agent revision
sequence. This pays rule preservation, not the missing source DCB axioms or
represented universally coded source apparatus, and is not KT consistency. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventual
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision

def Threshold (g : Ground) (initial : Extension) (σ : Sentence) (N : Nat) : Prop :=
  ∀ n, N ≤ n → σ.realize (stage g initial n) Fin.elim0

def Eventually (g : Ground) (initial : Extension) (σ : Sentence) : Prop :=
  ∃ N, Threshold g initial σ N

def allAgentsKnow (σ : Sentence) : Sentence :=
  .all (.imp (.agent (.var 0)) (.knowledge (.var 0) (Term.numeral (formulaCode σ))))
end LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventual
