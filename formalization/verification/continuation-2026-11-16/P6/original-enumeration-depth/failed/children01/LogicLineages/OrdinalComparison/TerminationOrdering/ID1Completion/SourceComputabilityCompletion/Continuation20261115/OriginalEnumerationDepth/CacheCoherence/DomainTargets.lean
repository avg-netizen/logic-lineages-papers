module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.DomainTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual stage coverage for the concrete totalized depth layer.
No assumption of layer success, guard calibration or cached value correctness. Some0 counts as present, while missing None does not. -/
def InternalStageDomain : Prop := ∀ (n : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (frontier old param table node found : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) table frontier old param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)) →
  Nonempty (Derivation body Delta (eqn found z).not)
/-- Domain of the actual raw-code-rank bounds successor graph at its actual subtraction
frontier. Previous graph and successful layer output witnesses are internal. -/
def InternalSuccessorDomain : Prop := ∀ (n : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (index seed param seedRank depth frontier table node found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank seedRank seed param)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) table (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)) →
  Nonempty (Derivation body Delta (eqn found z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.DomainTargets
