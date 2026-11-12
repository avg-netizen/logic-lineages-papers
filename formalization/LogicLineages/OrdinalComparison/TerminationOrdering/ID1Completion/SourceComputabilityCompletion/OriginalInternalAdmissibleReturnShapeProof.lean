module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (outputTransport equalEqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalAdmissibleReturnTargets OriginalInternalAdmissibleReturnBranchProof
open OriginalInternalJobAdmissible
open OriginalTypedDecoderInternalBranchProof (orCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consumerWeaken (R : Program 2) (input rest : OTerm alpha) (psi : Formula alpha)
 (next : Consumer body Delta R input rest psi) (Xi : List (Formula alpha))
 (hi : ∀ f ∈ Delta, f ∈ Xi) : Consumer body Xi R input rest psi := by
 intro beta j Theta out stack hj hp hs
 exact next beta j Theta out stack (fun f hf => hj f (hi f hf)) hp hs

theorem shapeCases (R : Program 2) (input work results frame rest payload role typ tag : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role role input)))
 (ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.raw) tag input)))
 (hshape : Nonempty (Derivation body Delta (ReturnShape role typ tag)))
 (next : Consumer body Delta R input rest psi) : Nonempty (Derivation body Delta psi) := by
 let A := equal role (numeral 0)
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ (equal tag (numeral 6) ⊔ equal tag (numeral 7)))
 apply orCases hshape
 · have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr0 := outputTransport OriginalHereditaryReturnStep.role role (numeral 0) (Fin.cons input Fin.elim0)
     (by simpa only [A,equalEqn] using he) (withHyp hr A)
   exact termCases R input work results frame rest payload psi (withHyp hs A) (withHyp hw A) (withHyp hf A) hr0
     (consumerWeaken R input rest psi next (A :: Delta) (fun f hf => List.mem_cons_of_mem _ hf))
 · have hB : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr1 := outputTransport OriginalHereditaryReturnStep.role role (numeral 1) (Fin.cons input Fin.elim0)
     (by simpa only [equalEqn] using andLeft hB) (withHyp hr B)
   apply orCases (andRight (andRight hB))
   · let C := equal tag (numeral 6)
     have hc : Nonempty (Derivation body (C :: B :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
     have ht6 := outputTransport (leftOf OriginalHereditaryReturnStep.raw) tag (numeral 6) (Fin.cons input Fin.elim0)
       (by simpa only [C,equalEqn] using hc) (withHyp (withHyp ht B) C)
     exact nilCases R input work results frame rest payload psi
       (withHyp (withHyp hs B) C) (withHyp (withHyp hw B) C) (withHyp (withHyp hf B) C)
       (withHyp hr1 C) ht6
       (consumerWeaken R input rest psi next (C :: B :: Delta) (fun f hf => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)))
   · let C := equal tag (numeral 7)
     have hc : Nonempty (Derivation body (C :: B :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
     have ht7 := outputTransport (leftOf OriginalHereditaryReturnStep.raw) tag (numeral 7) (Fin.cons input Fin.elim0)
       (by simpa only [C,equalEqn] using hc) (withHyp (withHyp ht B) C)
     exact consCases R input work results frame rest payload psi
       (withHyp (withHyp hs B) C) (withHyp (withHyp hw B) C) (withHyp (withHyp hf B) C)
       (withHyp hr1 C) ht7
       (consumerWeaken R input rest psi next (C :: B :: Delta) (fun f hf => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnShapeProof
