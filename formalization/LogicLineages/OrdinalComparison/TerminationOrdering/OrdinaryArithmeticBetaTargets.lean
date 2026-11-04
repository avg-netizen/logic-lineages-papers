module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaTargets

open OrdinaryArithmetic

def BetaTermTruth : Prop := ∀ {α : Type} (a b i r : Term α) (v : α → Nat),
  (betaFormula a b i r).Realize v ↔
    a.realize v % ((i.realize v + 1) * b.realize v + 1) = r.realize v

def ActualBetaTruth : Prop := ∀ n i r : Nat,
  betaGraph.Realize ![n.unpair.1, n.unpair.2, i, r] ↔ Nat.beta n i = r

def FiniteSequenceWitness : Prop := ∀ l : List Nat,
  ∃ a b : Nat, ∀ i : Fin l.length,
    betaGraph.Realize ![a, b, (i : Nat), l[i]]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaTargets
