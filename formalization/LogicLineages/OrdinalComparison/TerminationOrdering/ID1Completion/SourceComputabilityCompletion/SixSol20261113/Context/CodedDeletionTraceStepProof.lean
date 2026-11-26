module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn suc sucRelabel)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open CodedDeletionTraceInductionSyntax CodedDeletionTraceStateProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax CodedDeletionTraceElimination CodedDeletionTraceTransport
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem allRestrict (trace steps c : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllSteps trace (suc steps) c))) :
 Nonempty (Derivation body Delta (AllSteps trace steps c)) := by
 unfold AllSteps
 apply actualFiniteUniversalIntroduction body alpha 1 Delta
 unfold stepsBody
 let index : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := OriginalContextInsertion.Below index (steps.relabel Sum.inl)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 have h' := renameInto ha Sum.inl Theta
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [allRename,sucRelabel] at h'
 obtain ⟨ht⟩ := InternalOriginalOrderProof.actualOriginalOrderTransitivity body (alpha ⊕ Fin 1)
   index (steps.relabel Sum.inl) (suc (steps.relabel Sum.inl))
 obtain ⟨hf⟩ := andIntro
   (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   (InternalCoprimeMultipleBoundedProof.selfLtSucc (body := body) (Gamma := Theta) (steps.relabel Sum.inl))
 have hb := Nonempty.intro (Derivation.implicationElimination (InternalPositiveUnfoldingSupportProof.weakenClosed ht Theta) hf)
 obtain ⟨h⟩ := allApply (trace.relabel Sum.inl) (suc (steps.relabel Sum.inl)) (c.relabel Sum.inl) index h' hb
 exact ⟨Derivation.implicationIntroduction h⟩

theorem successorCore (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c left right parameter gamma : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R H G M W trace steps c)))
 (ha : Nonempty (Derivation body Delta (AllSteps trace (suc steps) c)))
 (hs : Nonempty (Derivation body Delta (StateAt trace (suc steps) left right parameter gamma))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) := by
 have hp := allRestrict trace steps c ha
 have ht := allApply trace (suc steps) c steps ha (InternalCoprimeMultipleBoundedProof.selfLtSucc steps)
 apply stepCases trace steps c _ ht
 intro beta j Theta v hj hv
 have hi' := renameInto hi j Theta hj
 have hp' := renameInto hp j Theta hj
 have hs' := renameInto hs j Theta hj
 rw [rowRename] at hi'
 rw [allRename] at hp'
 rw [stateRename,sucRelabel] at hs'
 rw [admittedRename]
 have hs0 := stateIntro (trace.relabel j) (steps.relabel j) (v 2) (v 3) (v 4) (v 5) (v 0)
   (andIntro (andLeft hv) (andLeft (andRight (andRight hv))))
 have hs1 := stateIntro (trace.relabel j) (suc (steps.relabel j)) (v 9) (v 10) (v 11) (v 12) (v 1)
   (andIntro (andLeft (andRight hv)) (andLeft (andRight (andRight (andRight (andRight hv))))))
 have hstart := rowApply R H G M W (trace.relabel j) (steps.relabel j) (c.relabel j) (v 2) (v 3) (v 4) (v 5) hi' hp' hs0
 have hnext := DeletionChainProof.step R H G M W (v 2) (v 3) (v 9) (v 10) (v 4) (v 11)
   (c.relabel j) (v 5) (v 12) (v 6) (v 7) (v 8) hstart
   (andRight (andRight (andRight (andRight (andRight hv)))))
 exact stateTransfer R H G M W (trace.relabel j) (suc (steps.relabel j))
   (v 9) (v 10) (v 11) (v 12) (left.relabel j) (right.relabel j) (parameter.relabel j) (gamma.relabel j)
   hs1 hs' hnext
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStepProof
