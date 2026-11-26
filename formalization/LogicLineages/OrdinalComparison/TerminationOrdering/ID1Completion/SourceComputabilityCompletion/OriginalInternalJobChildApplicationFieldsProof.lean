module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
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
theorem applicationFirst (H : Program 1) (M W : Program 2)
 (role typ raw payload inner domain fn arg arrow parameter c gamma cell annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (hdom : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain inner)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain typ)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 0) arrow)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 0) role typ raw cell parameter c gamma
  (numeral 0) arrow fn gamma parameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 2) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 2 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff H M W raw domain fn arg typ arrow gamma c hc ht) hterm
 have haccept := termAdmissible H M W arrow fn gamma c (andLeft (andRight facts))
 have hcell := firstCell raw cell parameter fn parameter hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationFirst (.projection 0) raw domain fn arg ys (projectionValue 0 ys) hc)
  (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 2 (by decide) ys parameter
   (OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) raw domain fn arg ys (projectionValue 0 ys) hc) (projectionValue 1 ys))
 have hannotation := OriginalInternalAnnotationChildValueProof.active (numeral 0) role typ raw (numeral 2) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc)
  (InternalSquareRootArithmeticSupportProof.strictTrans (numeral 0) (numeral 1) (numeral 2) (InternalCoprimeMultipleBoundedProof.selfLtSucc _) (InternalCoprimeMultipleBoundedProof.selfLtSucc _))
  (OriginalInternalAnnotationChildBinaryProof.application0 role typ raw payload domain inner arrow annotation hraw hdom ht ho)
 exact andIntro hcell (andIntro hp (andIntro ho (andIntro hannotation haccept)))
theorem applicationSecond (H : Program 1) (M W : Program 2)
 (role typ raw payload inner domain fn arg arrow parameter c gamma cell annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (hdom : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain inner)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain typ)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 0) domain)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 1) role typ raw cell parameter c gamma
  (numeral 0) domain arg gamma parameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 2) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 2 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff H M W raw domain fn arg typ arrow gamma c hc ht) hterm
 have haccept := termAdmissible H M W domain arg gamma c (andRight (andRight facts))
 have hcell := secondCell raw cell parameter arg hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationSecond (.projection 0) raw domain fn arg ys (projectionValue 0 ys) hc)
 have hannotation := OriginalInternalAnnotationChildValueProof.active (numeral 1) role typ raw (numeral 2) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc)
  (InternalCoprimeMultipleBoundedProof.selfLtSucc _)
  (OriginalInternalAnnotationChildBinaryProof.application1 (numeral 0) role typ raw payload domain inner annotation hraw hdom ho)
 exact andIntro hcell (andIntro hp (andIntro ho (andIntro hannotation haccept)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
