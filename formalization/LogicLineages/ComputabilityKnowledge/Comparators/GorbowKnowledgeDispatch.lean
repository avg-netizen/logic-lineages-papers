module

public import LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatch

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowKnowledgeDispatch
open GorbowSyntax GorbowSortedRevision GorbowSortedKnowledgeAxioms GorbowRegistryDispatch
open LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatch

def FixedClauses : Prop := ∀ (g : Ground) (P : Extension),
  nontriviality.realize (interpretation g P) Fin.elim0 ∧
  bridge.realize (interpretation g P) Fin.elim0 ∧
  veracity.realize (interpretation g P) Fin.elim0

def ClosureDistribution : Prop := ∀ (g : Ground), RelationLaws g → FunctionLaws g →
  ∀ P, MPClosed P → distribution.realize (interpretation g P) Fin.elim0

def SuccessorClosure : Prop := ∀ (g : Ground) P, MPClosed (revise g P)

def PositiveDistribution : Prop := ∀ (g : Ground), RelationLaws g → FunctionLaws g →
  ∀ initial k, distribution.realize (stage g initial (k+1)) Fin.elim0

def ConcreteInitial : Prop := MPClosed emptyInitial ∧
  (∀ c, ¬ emptyInitial c) ∧
  nontriviality.realize (stage GorbowAtomicRegistry.ground emptyInitial 0) Fin.elim0 ∧
  bridge.realize (stage GorbowAtomicRegistry.ground emptyInitial 0) Fin.elim0 ∧
  veracity.realize (stage GorbowAtomicRegistry.ground emptyInitial 0) Fin.elim0 ∧
  distribution.realize (stage GorbowAtomicRegistry.ground emptyInitial 0) Fin.elim0

def ConcreteAllStages : Prop := ∀ k,
  nontriviality.realize (stage GorbowAtomicRegistry.ground emptyInitial k) Fin.elim0 ∧
  bridge.realize (stage GorbowAtomicRegistry.ground emptyInitial k) Fin.elim0 ∧
  veracity.realize (stage GorbowAtomicRegistry.ground emptyInitial k) Fin.elim0 ∧
  distribution.realize (stage GorbowAtomicRegistry.ground emptyInitial k) Fin.elim0

def Target : Prop := FixedClauses ∧ ClosureDistribution ∧ SuccessorClosure ∧ PositiveDistribution ∧
  ConcreteInitial ∧ ConcreteAllStages
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowKnowledgeDispatch
