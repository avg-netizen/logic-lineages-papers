module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCases
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSupportProof (refl)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalTypedDecoderInternalBranchProof (orCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Source-supported role dispatch, separated from any runtime completion
assumption. All three callbacks consume literal original role/raw geometry. -/
theorem shapeCases (role typ raw tag rawPayload : OTerm alpha) (psi : Formula alpha)
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag rawPayload)))
 (hs : Nonempty (Derivation body Delta (ReturnShape role typ tag)))
 (termCase : ∀ Theta : List (Formula alpha), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (eqn role (numeral 0))) → Nonempty (Derivation body Theta psi))
 (nilCase : ∀ Theta : List (Formula alpha), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (eqn role (numeral 1))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)) →
   Nonempty (Derivation body Theta psi))
 (consCase : ∀ Theta : List (Formula alpha), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (eqn role (numeral 1))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)) →
   Nonempty (Derivation body Theta psi)) : Nonempty (Derivation body Delta psi) := by
 let A := equal role (numeral 0)
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ (equal tag (numeral 6) ⊔ equal tag (numeral 7)))
 apply orCases hs
 · apply termCase (A :: Delta) (fun f hf => List.mem_cons_of_mem _ hf)
   have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [A,equalEqn] using he
 · have hB : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hrole : Nonempty (Derivation body (B :: Delta) (eqn role (numeral 1))) := by
     simpa only [equalEqn] using andLeft hB
   apply orCases (andRight (andRight hB))
   · let C := equal tag (numeral 6)
     have ht : Nonempty (Derivation body (C :: B :: Delta) (eqn tag (numeral 6))) := by
       have he : Nonempty (Derivation body (C :: B :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
       simpa only [C,equalEqn] using he
     have hp := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing raw tag rawPayload
       (numeral 6) rawPayload ht ⟨refl rawPayload⟩ (withHyp (withHyp hr B) C)
     exact nilCase (C :: B :: Delta)
       (fun f hf => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)) (withHyp hrole C) hp
   · let C := equal tag (numeral 7)
     have ht : Nonempty (Derivation body (C :: B :: Delta) (eqn tag (numeral 7))) := by
       have he : Nonempty (Derivation body (C :: B :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
       simpa only [C,equalEqn] using he
     have hp := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing raw tag rawPayload
       (numeral 7) rawPayload ht ⟨refl rawPayload⟩ (withHyp (withHyp hr B) C)
     exact consCase (C :: B :: Delta)
       (fun f hf => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)) (withHyp hrole C) hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCases
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCases
