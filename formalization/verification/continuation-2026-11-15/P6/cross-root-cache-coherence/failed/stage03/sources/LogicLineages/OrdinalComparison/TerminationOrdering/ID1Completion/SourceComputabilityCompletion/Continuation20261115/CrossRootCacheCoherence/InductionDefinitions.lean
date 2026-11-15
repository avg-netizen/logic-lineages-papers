module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114

def fields {alpha : Type} (raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found : OTerm alpha) : Formula alpha :=
  PrimaryUncoveredCount.bounded index1 seed1 ⊓
  graph2 InternalEqualityTest.subtract depth1 index1 seed1 ⊓
  graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier1 depth1 seed1 param ⊓
  graph2 contains (numeral 1) frontier1 raw ⊓
  graph3 ArgumentEntriesRecursor.graph table1 (suc index1) seed1 param ⊓
  PrimaryUncoveredCount.bounded index2 seed2 ⊓
  graph2 InternalEqualityTest.subtract depth2 index2 seed2 ⊓
  graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier2 depth2 seed2 param ⊓
  graph2 contains (numeral 1) frontier2 raw ⊓
  graph3 ArgumentEntriesRecursor.graph table2 (suc index2) seed2 param ⊓
  graph2 ExchangeMapGraph.lookup found table1 raw
def result {alpha : Type} (raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found : OTerm alpha) : Formula alpha :=
  graph2 ExchangeMapGraph.lookup found table2 raw
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 12) :=
  (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11))).imp
  (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InductionDefinitions
