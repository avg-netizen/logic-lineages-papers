module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnPopProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalHereditaryReturnStepInternalSupportProof
open OriginalInternalAdmissibleReturnTargets
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem termCases (R : Program 2) (input work results frame rest payload : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (next : Consumer body Delta R input rest psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalAdmissibleReturnPopProof.popCases (OriginalHereditaryReturnStep.termValue R) input rest psi (restGraph input work results frame rest hs hw)
 intro beta j Theta out stack hj hpair hpop
 have hs' := renameInto hs j Theta hj
 have hw' := renameInto hw j Theta hj
 have hf' := renameInto hf j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hf' hr'
 exact next beta j Theta out stack hj hpair
  (control R (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j) out hs' hw' hf' (termRole R (input.relabel j) out hr' hpop))
theorem nilCases (R : Program 2) (input work results frame rest payload : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)))
 (ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.raw) (numeral 6) input)))
 (next : Consumer body Delta R input rest psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalAdmissibleReturnPopProof.popCases (OriginalRawSyntaxTransport.constant 1 0) input rest psi (restGraph input work results frame rest hs hw)
 intro beta j Theta out stack hj hpair hpop
 have hs' := renameInto hs j Theta hj
 have hw' := renameInto hw j Theta hj
 have hf' := renameInto hf j Theta hj
 have hr' := renameInto hr j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hf' hr' ht'
 let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 have hy := sameYesIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 6)
   (OriginalHereditaryReturnStep.pop (OriginalRawSyntaxTransport.constant 1 0)) (OriginalTypedDecoder.ifSame (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 7) (OriginalHereditaryReturnStep.pop OriginalHereditaryReturnStep.argumentsValue) (.projection 0))
   out (numeral 6) (numeral 6) xs ht' (constantValue 6 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Theta) (numeral 6)))) hpop
 exact next beta j Theta out stack hj hpair
  (control R (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j) out hs' hw' hf' (listRole R (input.relabel j) out hr' hy))
theorem consCases (R : Program 2) (input work results frame rest payload : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)))
 (ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.raw) (numeral 7) input)))
 (next : Consumer body Delta R input rest psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalAdmissibleReturnPopProof.popCases (OriginalHereditaryReturnStep.argumentsValue) input rest psi (restGraph input work results frame rest hs hw)
 intro beta j Theta out stack hj hpair hpop
 have hs' := renameInto hs j Theta hj
 have hw' := renameInto hw j Theta hj
 have hf' := renameInto hf j Theta hj
 have hr' := renameInto hr j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hf' hr' ht'
 let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 have hy := sameYesIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 7)
   (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.argumentsValue)) (.projection 0)
   out (numeral 7) (numeral 7) xs ht' (constantValue 7 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Theta) (numeral 7)))) hpop
 have hy' := sameNoIntro (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 6)
   (OriginalHereditaryReturnStep.pop (OriginalRawSyntaxTransport.constant 1 0))
   (OriginalTypedDecoder.ifSame (leftOf OriginalHereditaryReturnStep.raw) (OriginalRawSyntaxTransport.constant 1 7) (OriginalHereditaryReturnStep.pop OriginalHereditaryReturnStep.argumentsValue) (.projection 0))
   out (numeral 7) (numeral 6) xs ht' (constantValue 6 xs) (numeralNe 7 6 (by decide)) hy
 exact next beta j Theta out stack hj hpair
  (control R (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j) out hs' hw' hf' (listRole R (input.relabel j) out hr' hy'))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnBranchProof
