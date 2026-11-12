module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalCombinedRootProjectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalCombinedRootProjectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesElim sameNoElim nonzeroAtElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem recover (R : Program 2) (input work results frame rest payload out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) out input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hwork := OriginalHereditaryInternalVisitSupportProof.workGraph input work results hs
 have hframe := OriginalHereditaryInternalVisitSupportProof.frameGraph input work results frame rest hs hw
 have htag : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryCombinedStep.frame) (numeral 1) input)) :=
   unaryValue InternalUnpair.left OriginalHereditaryCombinedStep.frame (numeral 1) frame xs (pairLeft frame (numeral 1) payload hf) hframe
 have hn := nonzeroAtElim OriginalHereditaryCombinedStep.work (.projection 0) _ out work xs hwork
   (OriginalTypedDecoderInternalListProof.consNonzero work frame rest hw) hr
 have hy := sameNoElim (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 0)
   OriginalHereditaryAnnotatedVisit.step _ out (numeral 1) (numeral 0) xs htag (constantValue 0 xs) (numeralNe 1 0 (by decide)) hn
 exact sameYesElim (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 1)
   (OriginalHereditaryReturnStep.step R) (.projection 0) out (numeral 1) (numeral 1) xs htag (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hy

theorem actualProjection : OriginalInternalCombinedRootProjectionTargets.ActualProjection := by
 intro R body alpha Delta input work results frame rest payload packed parameter out outWork stack value old root tail
   hs hw hf hrole hpacked hparameter hstep hout hstack hvalue
 exact OriginalInternalReturnRootProjectionProof.actualProjection R body alpha Delta input work results frame rest payload packed parameter out outWork stack value old root tail
   hs hw hf hrole hpacked hparameter (recover R input work results frame rest payload out hs hw hf hstep) hout hstack hvalue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalCombinedRootProjectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalCombinedRootProjectionProof
