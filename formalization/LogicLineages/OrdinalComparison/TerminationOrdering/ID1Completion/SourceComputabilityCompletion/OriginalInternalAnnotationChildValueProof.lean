module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedExpansion
open OriginalInternalAnnotationChildDispatchProof
open InternalTagArithmeticSyntaxProof (z suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem active (index role typ raw arity out : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity raw)))
 (hb : Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF index arity)))
 (hv : Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 annotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have ha' := OriginalRawSyntaxTransportInternalConstructorSubstitutionProof.arityValueAt
  (.projection 3) arity raw xs (projectionValue 3 xs) ha
 have ht := binaryValue InternalLessThan.ltTest (.projection 0) (OriginalRawSyntaxTransport.arityOf (.projection 3))
  (suc z) index arity xs (InternalLessThanSupportProof.acceptOfLess index arity hb) (projectionValue 0 xs) ha'
 exact InternalPathCheckerBranchProof.nonzeroBranchIntro _ inherited childAnnotation out (suc z) xs ht
  ⟨InternalTagArithmeticSupportProof.sucNeZero z⟩ hv
theorem tagAt (index role typ raw tag payload : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))) :
 Nonempty (Derivation body Delta (graph4 parentTag tag index role typ raw)) :=
 unaryValue InternalUnpair.left (.projection 3) tag raw ![index,role,typ,raw]
  (pairLeft raw tag payload hp) (projectionValue 3 ![index,role,typ,raw])
theorem domainAt (index role typ raw tag payload dom inner : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload dom inner))) :
 Nonempty (Derivation body Delta (graph4 domain dom index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h := unaryValue InternalUnpair.right (.projection 3) payload raw xs (pairRight raw tag payload hp) (projectionValue 3 xs)
 exact unaryValue InternalUnpair.left (rightOf (.projection 3)) dom payload xs (pairLeft payload dom inner hd) h
theorem lambdaValue (index role typ raw payload dom cod out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ dom cod)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) cod))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have hc := unaryValue InternalListCodec.tailCode (.projection 2) cod typ xs
  (InternalRawListRecursionSupportProof.consTail typ dom cod ht) (projectionValue 2 xs)
 have hv := binaryValue InternalPairing.pairing (constant 4 0)
  (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 2)) out (numeral 0) cod xs ho (constantValue 0 xs) hc
 exact dispatch1 index role typ raw out (tagAt index role typ raw (numeral 1) payload hp) hv
theorem listValue (index role typ raw out : OTerm alpha)
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) (numeral 0)))) :
 Nonempty (Derivation body Delta (graph4 listAnnotation out index role typ raw)) :=
 binaryValue InternalPairing.pairing (constant 4 1) (constant 4 0) out (numeral 1) (numeral 0)
  ![index,role,typ,raw] ho (constantValue 1 _) (constantValue 0 _)
theorem ordinaryValue (index role typ raw payload out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) (numeral 0)))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) :=
 dispatch4 index role typ raw out (tagAt index role typ raw (numeral 4) payload hp) (listValue index role typ raw out ho)
theorem numberedValue (index role typ raw payload out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) (numeral 0)))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) :=
 dispatch5 index role typ raw out (tagAt index role typ raw (numeral 5) payload hp) (listValue index role typ raw out ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildValueProof
