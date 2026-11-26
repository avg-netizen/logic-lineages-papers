module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedExpansion
open OriginalInternalAnnotationChildDispatchProof OriginalInternalAnnotationChildValueProof
open InternalTagArithmeticSyntaxProof (z suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem application0 (role typ raw payload dom inner arrow out: OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload dom inner)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow dom typ)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) arrow))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out z role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![z,role,typ,raw]
 have ht := tagAt z role typ raw (numeral 2) payload hp
 have hdv := domainAt z role typ raw (numeral 2) payload dom inner hp hd
 have hav := binaryValue InternalListCodec.consCode domain (.projection 2) arrow dom typ xs ha hdv (projectionValue 2 xs)
 have hv := binaryValue InternalPairing.pairing (constant 4 0) (consOf domain (.projection 2)) out (numeral 0) arrow xs ho (constantValue 0 xs) hav
 have hb := InternalAcceptanceBranchProof.zeroBranchIntro (.projection 0) (termAnnotation (consOf domain (.projection 2))) (termAnnotation domain) out xs (projectionValue 0 xs) hv
 exact dispatch2 z role typ raw out ht hb
theorem application1 (index role typ raw payload dom inner out: OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload dom inner)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) dom))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out (suc index) role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![(suc index),role,typ,raw]
 have ht := tagAt (suc index) role typ raw (numeral 2) payload hp
 have hdv := domainAt (suc index) role typ raw (numeral 2) payload dom inner hp hd
 have hv := binaryValue InternalPairing.pairing (constant 4 0) domain out (numeral 0) dom xs ho (constantValue 0 xs) hdv
 have hb := InternalPathCheckerBranchProof.nonzeroBranchIntro (.projection 0) (termAnnotation (consOf domain (.projection 2))) (termAnnotation domain) out (suc index) xs (projectionValue 0 xs) ⟨InternalTagArithmeticSupportProof.sucNeZero index⟩ hv
 exact dispatch2 (suc index) role typ raw out ht hb
theorem cons0 (role typ raw payload dom inner out: OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) payload)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload dom inner)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) dom))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out z role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![z,role,typ,raw]
 have ht := tagAt z role typ raw (numeral 7) payload hp
 have hdv := domainAt z role typ raw (numeral 7) payload dom inner hp hd
 have hv := binaryValue InternalPairing.pairing (constant 4 0) domain out (numeral 0) dom xs ho (constantValue 0 xs) hdv
 have hb := InternalAcceptanceBranchProof.zeroBranchIntro (.projection 0) (termAnnotation domain) listAnnotation out xs (projectionValue 0 xs) hv
 exact dispatch7 z role typ raw out ht hb
theorem cons1 (index role typ raw payload dom inner out: OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) payload)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload dom inner)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) (numeral 0)))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out (suc index) role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![(suc index),role,typ,raw]
 have ht := tagAt (suc index) role typ raw (numeral 7) payload hp
 have hdv := domainAt (suc index) role typ raw (numeral 7) payload dom inner hp hd
 have hv := listValue (suc index) role typ raw out ho
 have hb := InternalPathCheckerBranchProof.nonzeroBranchIntro (.projection 0) (termAnnotation domain) listAnnotation out (suc index) xs (projectionValue 0 xs) ⟨InternalTagArithmeticSupportProof.sucNeZero index⟩ hv
 exact dispatch7 (suc index) role typ raw out ht hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
