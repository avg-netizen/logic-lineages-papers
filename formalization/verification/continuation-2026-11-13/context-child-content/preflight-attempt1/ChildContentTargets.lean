module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions
/-- The original application child prefix, not a supplied pair of semantic
child computations, pays the two scalar slots consumed by actual returnRoot.
The map reads the literal two-job scan prefix in original order. This is local
content provenance; no evaluator correctness or fixedpoint is assumed. -/
def ApplicationReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw domain fnRaw argRaw fnType parameter jobs prefix row first tail second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain fnRaw argRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefix (numeral 2) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row prefix)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first tail)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

/-- The original argument-cons prefix contains a term job then an argument-list
job. Its actual mapped slots pay the head scalar and original tail observation
consumed by actual returnArgumentsCons, without supplying either child law. -/
def ArgumentsConsReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw typ child tailRaw parameter jobs prefix row first tail second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tailRaw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefix (numeral 2) (numeral 1) z raw jobs)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row prefix)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first tail)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons returned raw first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) returned raw parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
