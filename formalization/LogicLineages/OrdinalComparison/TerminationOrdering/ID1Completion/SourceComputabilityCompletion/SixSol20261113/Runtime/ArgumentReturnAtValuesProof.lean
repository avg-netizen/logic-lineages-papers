module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentChildContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnValueAgreementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnAtValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
theorem nil (R Q : Program 2) (job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral 0) raw)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)))
 (hnil : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
 have hcanonical := UniformReturnListFrameProof.nilFrame R job typed (numeral 0) rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload hj ht hr hc hp hframe hpacked htag hs
 have he := ArgumentReturnValueAgreementProof.agreement R frame produced (numeral 0) value hcanonical hf
 exact outputTransport (OriginalTypedArgumentObservations.argumentObservations Q) (numeral 0) value (Fin.cons raw (Fin.cons parameter Fin.elim0)) he
   (OriginalTypedArgumentObservationsInternalNilProof.nilValue Q raw parameter hnil)
theorem consAtValue (R Q : Program 2) (job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value : OTerm alpha)
 (domain child tailRaw rawJobs annotatedPrefix childRow returned : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral 0) raw)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
 (hcon : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain child tailRaw)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children (numeral 1) (numeral 0) raw rawJobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph children childRow)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (numeral 0) childRow)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow)))
 (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons returned raw first second)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
 have harity2 := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consArity (.projection 0) raw domain child tailRaw (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hcon
 have hcount := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (numeral 2) (Fin.cons raw Fin.elim0) harity harity2
 have hscan2 := headTransport OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children (numeral 2)
   (Fin.cons (numeral 1) (Fin.cons (numeral 0) (Fin.cons raw (Fin.cons rawJobs Fin.elim0)))) hcount hscan
 have hlen2 := outputTransport OriginalContextInsertion.length children (numeral 2) (Fin.cons childRow Fin.elim0) hcount hlen
 have hsemantic := ArgumentChildContentProof.cons Q raw domain child tailRaw parameter rawJobs annotatedPrefix childRow first second returned hcon he hscan2 hm hlen2 hfirst hsecond hret
 have hcanonical := UniformReturnListFrameProof.consFrame R job typed (numeral 0) rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload returned hj ht hr hc hp hframe hpacked htag hret hs
 have heq := ArgumentReturnValueAgreementProof.agreement R frame produced returned value hcanonical hf
 exact outputTransport (OriginalTypedArgumentObservations.argumentObservations Q) returned value (Fin.cons raw (Fin.cons parameter Fin.elim0)) heq hsemantic

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnAtValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnAtValuesProof
