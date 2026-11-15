module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- An actual frontier member fits the index budget, obtained from the literal
subtraction graph and internal depth+node bound, not from native calibration. -/
def InternalCapacity : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed param depth frontier node : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded node index))
/-- Child lookup in the actual previous graph stage is present, deriving its
required depth+1 alignment from the current successor index subtraction.
This is presence only, not equality to an independently rooted child value. -/
def InternalAlignedPreviousCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed param depth frontier previous node deps child found : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (suc index) seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth (suc index) seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph previous (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found previous child)) →
  Nonempty (Derivation body Delta (eqn found z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
