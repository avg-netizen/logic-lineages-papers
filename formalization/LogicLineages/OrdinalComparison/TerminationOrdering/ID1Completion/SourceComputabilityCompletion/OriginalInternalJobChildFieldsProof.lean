module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
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
theorem ordinaryFirst (H : Program 1) (M W : Program 2)
 (role typ raw payload head base parameter c gamma cell headData result types annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 1) (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 0) role typ raw cell parameter c gamma
  (numeral 1) (numeral 0) base gamma parameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.ordinaryTag (.projection 0) raw head base xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 4) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 4 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H M W raw head base headData result types typ gamma c hc hh ht) hterm
 have haccept := listAdmissible H M W types base gamma c (andRight (andRight (andRight (andRight facts))))
 have hcell := firstCell raw cell parameter base parameter hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryFirst (.projection 0) raw head base ys (projectionValue 0 ys) hc)
  (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 4 (by decide) ys parameter
   (OriginalRawSyntaxTransportInternalConstructorFieldsProof.ordinaryTag (.projection 0) raw head base ys (projectionValue 0 ys) hc) (projectionValue 1 ys))
 have hannotation := OriginalInternalAnnotationChildValueProof.active (numeral 0) role typ raw (numeral 1) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryArity (.projection 0) raw head base xs (projectionValue 0 xs) hc)
  (InternalCoprimeMultipleBoundedProof.selfLtSucc _)
  (OriginalInternalAnnotationChildValueProof.ordinaryValue (numeral 0) role typ raw payload annotation hraw ho)
 exact andIntro hcell (andIntro hp (andIntro ho (andIntro hannotation haccept)))

theorem numberedFirst (H : Program 1) (M W : Program 2)
 (role typ raw payload label head recorded base extraTypes extras parameter c gamma cell headData result types annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 1) (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 0) role typ raw cell parameter c gamma
  (numeral 1) (numeral 0) base gamma parameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) raw label head recorded base extraTypes extras xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 5) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 5 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W raw label head recorded base extraTypes extras headData result types typ gamma c hc hh ht) hterm
 have children := andRight (andRight (andRight (andRight facts)))
 have haccept := listAdmissible H M W types base gamma c (andLeft children)
 have hcell := firstCell raw cell parameter base parameter hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedFirst (.projection 0) raw label head recorded base extraTypes extras ys (projectionValue 0 ys) hc)
  (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 5 (by decide) ys parameter
   (OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) raw label head recorded base extraTypes extras ys (projectionValue 0 ys) hc) (projectionValue 1 ys))
 have hannotation := OriginalInternalAnnotationChildValueProof.active (numeral 0) role typ raw (numeral 2) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity (.projection 0) raw label head recorded base extraTypes extras xs (projectionValue 0 xs) hc)
  (InternalSquareRootArithmeticSupportProof.strictTrans (numeral 0) (numeral 1) (numeral 2) (InternalCoprimeMultipleBoundedProof.selfLtSucc _) (InternalCoprimeMultipleBoundedProof.selfLtSucc _))
  (OriginalInternalAnnotationChildValueProof.numberedValue (numeral 0) role typ raw payload annotation hraw ho)
 exact andIntro hcell (andIntro hp (andIntro ho (andIntro hannotation haccept)))

theorem numberedSecond (H : Program 1) (M W : Program 2)
 (role typ raw payload label head recorded base extraTypes extras parameter c gamma cell headData result types annotation : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation (numeral 1) (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Packet H M W (numeral 1) role typ raw cell parameter c gamma
  (numeral 1) (numeral 0) extras gamma parameter annotation)) := by
 let xs : Fin 1 → OTerm alpha := ![raw]
 let ys : Fin 2 → OTerm alpha := ![raw,parameter]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) raw label head recorded base extraTypes extras xs (projectionValue 0 xs) hc
 have htagRaw := unaryRecover InternalUnpair.left (.projection 0) (numeral 5) raw xs htag (projectionValue 0 xs)
 have hterm := termAtTag H M W 5 (by decide) (by decide) role typ raw gamma c ha htagRaw
 have facts := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W raw label head recorded base extraTypes extras headData result types typ gamma c hc hh ht) hterm
 have children := andRight (andRight (andRight (andRight facts)))
 have haccept := listAdmissible H M W extraTypes extras gamma c (andRight children)
 have hcell := secondCell raw cell parameter extras hj
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedSecond (.projection 0) raw label head recorded base extraTypes extras ys (projectionValue 0 ys) hc)
 have hannotation := OriginalInternalAnnotationChildValueProof.active (numeral 1) role typ raw (numeral 2) annotation
  (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity (.projection 0) raw label head recorded base extraTypes extras xs (projectionValue 0 xs) hc)
  (InternalCoprimeMultipleBoundedProof.selfLtSucc _)
  (OriginalInternalAnnotationChildValueProof.numberedValue (numeral 1) role typ raw payload annotation hraw ho)
 exact andIntro hcell (andIntro hp (andIntro ho (andIntro hannotation haccept)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
