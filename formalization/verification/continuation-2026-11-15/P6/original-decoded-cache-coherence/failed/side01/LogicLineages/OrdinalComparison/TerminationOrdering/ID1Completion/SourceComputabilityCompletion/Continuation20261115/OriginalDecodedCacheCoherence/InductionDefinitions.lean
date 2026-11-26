module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} (budget node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha) : Formula alpha :=
  graph2 (OriginalDecodedRank.rank n) budget node param ⊓
  graph2 (OriginalDecodedRank.rank n) rank1 seed1 param ⊓
  PrimaryUncoveredCount.bounded index1 rank1 ⊓
  graph2 InternalEqualityTest.subtract depth1 index1 rank1 ⊓
  graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier1 depth1 seed1 param ⊓
  graph2 contains (numeral 1) frontier1 node ⊓
  graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table1 (suc index1) seed1 param ⊓
  graph2 (OriginalDecodedRank.rank n) rank2 seed2 param ⊓
  PrimaryUncoveredCount.bounded index2 rank2 ⊓
  graph2 InternalEqualityTest.subtract depth2 index2 rank2 ⊓
  graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier2 depth2 seed2 param ⊓
  graph2 contains (numeral 1) frontier2 node ⊓
  graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table2 (suc index2) seed2 param ⊓
  graph2 ExchangeMapGraph.lookup found table1 node
def result {alpha : Type} (budget node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha) : Formula alpha :=
  graph2 ExchangeMapGraph.lookup found table2 node
def matrix (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} (budget : OTerm alpha) : Formula (alpha ⊕ Fin 15) :=
  (fields n arity V (budget.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11)) (.var (.inr 12)) (.var (.inr 13)) (.var (.inr 14))).imp
    (result (budget.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11)) (.var (.inr 12)) (.var (.inr 13)) (.var (.inr 14)))
def AtRaw (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} (budget : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n arity V budget)
def rawPredicate (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw n arity V (.var (.inr 0))
def BelowRaw (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} (budget : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate n arity V) budget
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionDefinitions
