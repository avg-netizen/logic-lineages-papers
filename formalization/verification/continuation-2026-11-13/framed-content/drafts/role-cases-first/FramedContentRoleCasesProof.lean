module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentRoleCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Original admission restricts the actual job role, without asking a caller
for a role split or a syntactic well-formedness oracle. -/
theorem fieldsCases (H : Program 1) (M W : Program 2)
 (job role typed typ raw gamma c : OTerm alpha) (psi : Formula alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (zero : ∀ Theta : List (Formula alpha), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 InternalUnpair.left (numeral 0) job)) →
   Nonempty (Derivation body Theta psi))
 (one : ∀ Theta : List (Formula alpha), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 InternalUnpair.left (numeral 1) job)) →
   Nonempty (Derivation body Theta psi)) : Nonempty (Derivation body Delta psi) := by
 apply OriginalTypedDecoderInternalBranchProof.orCases ha
 · let A := equal role (numeral 0) ⊓ OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c
   have hh : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he := andLeft hh
   rw [equalEqn] at he
   have hl := pairLeft job role typed (withHyp hj A)
   exact zero (A :: Delta) (fun f hf => List.mem_cons_of_mem _ hf)
     (outputTransport InternalUnpair.left role (numeral 0) (Fin.cons job Fin.elim0) he hl)
 · let A := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ OriginalInternalJobAdmissible.ArgumentsWitness H M W raw gamma c)
   have hh : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he := andLeft hh
   rw [equalEqn] at he
   have hl := pairLeft job role typed (withHyp hj A)
   exact one (A :: Delta) (fun f hf => List.mem_cons_of_mem _ hf)
     (outputTransport InternalUnpair.left role (numeral 1) (Fin.cons job Fin.elim0) he hl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentRoleCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentRoleCasesProof
