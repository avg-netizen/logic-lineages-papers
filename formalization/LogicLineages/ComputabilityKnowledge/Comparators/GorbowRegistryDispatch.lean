module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDispatch
open GorbowSyntax GorbowSortedRevision
open LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch

def OriginalGround : Prop := RelationLaws GorbowSortedRegistry.ground ∧ FunctionLaws GorbowSortedRegistry.ground

def BooleanClauses : Prop := ∀ g, RelationLaws g → FunctionLaws g → ∀ initial k,
  (GorbowBooleanTruth.negAxiom).realize (stage g initial (k+1)) Fin.elim0 ∧
  (GorbowBooleanTruth.impAxiom).realize (stage g initial (k+1)) Fin.elim0 ∧
  (GorbowBooleanTruth.conjAxiom).realize (stage g initial (k+1)) Fin.elim0 ∧
  (GorbowBooleanTruth.disjAxiom).realize (stage g initial (k+1)) Fin.elim0

def QuantifierClauses : Prop := ∀ g, RelationLaws g → FunctionLaws g → ∀ initial k,
  (GorbowSortedQuantifierTruth.forallAxiom).realize (stage g initial (k+1)) Fin.elim0 ∧
  (GorbowSortedQuantifierTruth.existsAxiom).realize (stage g initial (k+1)) Fin.elim0 ∧
  (GorbowSortedQuantifierTruth.barcanAxiom).realize (stage g initial (k+1)) Fin.elim0

def Target : Prop := OriginalGround ∧ BooleanClauses ∧ QuantifierClauses
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDispatch
