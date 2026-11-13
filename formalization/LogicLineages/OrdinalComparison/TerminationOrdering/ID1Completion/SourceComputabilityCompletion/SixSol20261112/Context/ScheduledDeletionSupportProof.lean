module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationOffsetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open ScheduledDeletionDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListCodec.consCode OriginalHereditaryAnnotatedExpansion.annotation
  OriginalRawSyntaxTransport.erasePackedRaw

/-- Recover the actual decorated job pair from the actual inherited annotation.
The raw job is copied by the unchanged decorate AST. -/
theorem decoratedPair (index role typ raw rawCell annotated annotation typed : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.annotation annotation index role typ raw)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation role typ)))
    (htp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawCell)))
    (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate annotated index role typ raw rawCell))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotated role typed)) := by
  let xs : Fin 5 → OTerm alpha := ![index,role,typ,raw,rawCell]
  let a : Program 5 := .composition OriginalHereditaryAnnotatedExpansion.annotation
    ![.projection 0,.projection 1,.projection 2,.projection 3]
  have av : Nonempty (Derivation body Delta (programGraph a annotation xs)) := by
    apply compositionValue OriginalHereditaryAnnotatedExpansion.annotation
      ![.projection 0,.projection 1,.projection 2,.projection 3] annotation xs
      ![index,role,typ,raw] ha
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i
    · exact projectionValue 0 xs
    · exact projectionValue 1 xs
    · exact projectionValue 2 xs
    · exact projectionValue 3 xs
  have leftValue := unaryValue InternalUnpair.left a role annotation xs
    (pairLeft annotation role typ hap) av
  have rightValue := unaryValue InternalUnpair.right a typ annotation xs
    (pairRight annotation role typ hap) av
  have typedValue := binaryValue InternalPairing.pairing (rightOf a) (.projection 4)
    typed typ rawCell xs htp rightValue (projectionValue 4 xs)
  exact binaryRecover InternalPairing.pairing (leftOf a) (pairOf (rightOf a) (.projection 4))
    annotated role typed xs hd leftValue typedValue

/-- An actual fixed Q call at the stored job coordinates is recovered through
the literal annotated-job encoding, with no native evaluator semantics. -/
theorem scalarAtPairs (Q : Program 2)
    (annotated role typed typ rawCell erased childParameter packed value : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotated role typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawCell)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell erased childParameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ erased)))
    (hv : Nonempty (Derivation body Delta (graph1 (scalarFromJob Q) value annotated))) :
    Nonempty (Derivation body Delta (graph2 Q value packed childParameter)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons annotated Fin.elim0
  have inner := unaryValue InternalUnpair.right (.projection 0) typed annotated xs
    (pairRight annotated role typed hn) (projectionValue 0 xs)
  have typeValue := unaryValue InternalUnpair.left (rightOf (.projection 0)) typ typed xs
    (pairLeft typed typ rawCell ht) inner
  have rawJobValue := unaryValue InternalUnpair.right (rightOf (.projection 0)) rawCell typed xs
    (pairRight typed typ rawCell ht) inner
  have rawValue := unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) erased rawCell xs
    (pairLeft rawCell erased childParameter hr) rawJobValue
  have parameterValue := unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) childParameter rawCell xs
    (pairRight rawCell erased childParameter hr) rawJobValue
  have packedValue := binaryValue InternalPairing.pairing jobType jobRaw packed typ erased xs
    hp typeValue rawValue
  exact binaryRecover Q jobPacked jobParameter value packed childParameter xs hv packedValue parameterValue

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof.decoratedPair
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionSupportProof.scalarAtPairs
