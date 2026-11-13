module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalClassContextAllPositionObserver OriginalContextInsertion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ObservedAllTestsDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSupportProof
open InternalOriginalOrderProof
open InternalSquareRootArithmeticSupportProof (rightSuccessor)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ObservedAllTestsSyntax

theorem boundedRestrict (R : Program 2) (count seed candidate parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (BoundedTests R (suc count) seed candidate parameter))) :
 Nonempty (Derivation body Delta (BoundedTests R count seed candidate parameter)) := by
 unfold BoundedTests
 apply actualFiniteUniversalIntroduction body alpha 1 Delta
 unfold boundedMatrix
 let cutoff : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := Below cutoff (count.relabel Sum.inl)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 have h' := renameInto h Sum.inl Theta
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [boundedRename] at h'
 simp only [sucRelabel] at h'
 have hb : Nonempty (Derivation body Theta (Below cutoff (suc (count.relabel Sum.inl)))) :=
   rightSuccessor cutoff (count.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨out⟩ := boundedApply R (suc (count.relabel Sum.inl)) (seed.relabel Sum.inl)
   (candidate.relabel Sum.inl) (parameter.relabel Sum.inl) cutoff h' hb
 exact ⟨Derivation.implicationIntroduction out⟩
theorem selfBelowSuccessor (count : OTerm alpha) :
 Nonempty (Derivation body Delta (Below count (suc count))) := by
 apply actualOriginalOrderIntroduction body alpha Delta count (suc count) z
 rw [onEquality]
 exact ⟨trans (addSucc count z) (congSuc (addZero count))⟩
theorem zeroRow (R : Program 2) (seed candidate parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (row R z seed candidate parameter)) := by
 obtain ⟨h⟩ := OriginalAllPositionRelationScanStepProof.zeroAccepted R seed candidate parameter
   (body := body) (Delta := BoundedTests R z seed candidate parameter :: Delta)
 exact ⟨Derivation.implicationIntroduction h⟩
theorem successorRow (R : Program 2) (count seed candidate parameter : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R count seed candidate parameter))) :
 Nonempty (Derivation body Delta (row R (suc count) seed candidate parameter)) := by
 let A := BoundedTests R (suc count) seed candidate parameter
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨prior⟩ := boundedRestrict R count seed candidate parameter h
 obtain ⟨ih⟩ := withHyp hi A
 have hs : Nonempty (Derivation body (A :: Delta) (graph4 (scan R) (suc z) count seed candidate parameter)) :=
   ⟨Derivation.implicationElimination ih prior⟩
 have ht := boundedApply R (suc count) seed candidate parameter count h (selfBelowSuccessor count)
 obtain ⟨out⟩ := OriginalAllPositionRelationScanStepProof.successorAccepted R count seed candidate parameter hs ht
 exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsCoreProof
