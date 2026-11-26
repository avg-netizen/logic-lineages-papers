module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalInternalJobAdmissible OriginalInternalJobChildPacket OriginalInternalJobChildSupportProof
open OriginalInternalJobAcceptedChildrenProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderTransportLogicalProof
open OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lambdaFirst (H : Program 1) (M W : Program 2)
 (role typ raw payload domain child requested codomain extended childParameter parameter c gamma cell annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields typ requested codomain)))
 (htail : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode codomain typ)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 0) codomain)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 0) role typ raw cell parameter c gamma
  (numeral 0) codomain child extended childParameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.lambdaTag (.projection 0) raw domain child xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 1) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 1 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.lambdaIff H M W raw domain child typ requested codomain gamma extended c hc ht he) hterm
 have haccept := termAdmissible H M W codomain child extended c (andRight (andRight (andRight (andRight facts))))
 have hcell := firstCell raw cell parameter child childParameter hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaFirst (.projection 0) raw domain child ys (projectionValue 0 ys) hc)
  (OriginalHereditaryInternalExpansionLambdaParameterProof.parameterValue raw domain child parameter c gamma extended childParameter hc hp he hcp)
 let zs : Fin 4 → OTerm alpha := ![numeral 0,role,typ,raw]
 have hcod := unaryValue InternalListCodec.tailCode (.projection 2) codomain typ zs htail (projectionValue 2 zs)
 have hv := binaryValue InternalPairing.pairing (constant 4 0)
  (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 2)) annotation (numeral 0) codomain zs ho
  (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 zs) hcod
 have hchild := OriginalInternalAnnotationChildDispatchProof.dispatch1 (numeral 0) role typ raw annotation
  (OriginalInternalAnnotationChildValueProof.tagAt (numeral 0) role typ raw (numeral 1) payload hraw) hv
 have hann := OriginalInternalAnnotationChildValueProof.active (numeral 0) role typ raw (numeral 1) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaArity (.projection 0) raw domain child xs (projectionValue 0 xs) hc)
  (InternalCoprimeMultipleBoundedProof.selfLtSucc _) hchild
 exact andIntro hcell (andIntro hcp (andIntro ho (andIntro hann haccept)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaFieldsProof
