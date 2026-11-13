module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel emb varBind liftBind)
open InternalAdditionLawsProof (liftNext varNext)
open InternalTagArithmeticSupportProof (natInduction)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open CodedDeletionTraceStepProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open CodedDeletionTraceInductionSyntax CodedDeletionTraceStateProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax CodedDeletionTraceElimination CodedDeletionTraceTransport
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace c left right parameter gamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (StateAt trace z left right parameter gamma)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))) :
 Nonempty (Derivation body Delta (row R H G M W trace z c)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 unfold rowBody
 simp only [zRelabel]
 let v : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
 let A := AllSteps (trace.relabel Sum.inl) z (c.relabel Sum.inl) ⊓
   StateAt (trace.relabel Sum.inl) z (v 0) (v 1) (v 2) (v 3)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hs' := renameInto hs Sum.inl Theta
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have ha' := renameInto ha Sum.inl Theta
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [stateRename,zRelabel] at hs'
 rw [admittedRename] at ha'
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := stateTransfer R H G M W (trace.relabel Sum.inl) z
   (left.relabel Sum.inl) (right.relabel Sum.inl) (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
   (v 0) (v 1) (v 2) (v 3) hs' (andRight hh) ha'
 exact ⟨Derivation.implicationIntroduction h⟩
theorem successorRow (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R H G M W trace steps c))) :
 Nonempty (Derivation body Delta (row R H G M W trace (suc steps) c)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 unfold rowBody
 simp only [sucRelabel]
 let v : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
 let A := AllSteps (trace.relabel Sum.inl) (suc (steps.relabel Sum.inl)) (c.relabel Sum.inl) ⊓
   StateAt (trace.relabel Sum.inl) (suc (steps.relabel Sum.inl)) (v 0) (v 1) (v 2) (v 3)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hi' := renameInto hi Sum.inl Theta
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [rowRename] at hi'
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := successorCore R H G M W (trace.relabel Sum.inl) (steps.relabel Sum.inl) (c.relabel Sum.inl)
   (v 0) (v 1) (v 2) (v 3) hi' (andLeft hh) (andRight hh)
 exact ⟨Derivation.implicationIntroduction h⟩
/-- The induction variable is an actual arithmetic term; the trace and source
assumptions stay in the object-theory environment throughout induction. -/
theorem allRows (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c left right parameter gamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (StateAt trace z left right parameter gamma)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))) :
 Nonempty (Derivation body Delta (row R H G M W trace steps c)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row R H G M W (trace.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl)
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind,liftBind] using (zeroRow R H G M W trace c left right parameter gamma hs ha)
 have hsucc : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow R H G M W (body := body) (Delta := theta :: Delta.map weaken)
     (trace.relabel Sum.inl) (.var (.inr (0 : Fin 1))) (c.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,liftNext,varNext] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hsucc⟩ := hsucc
 have h := Derivation.universalElimination (emb steps) (natInduction theta hz hsucc)
 simpa only [theta,rowInstantiate,varBind,liftBind] using Nonempty.intro h

theorem actualCodedChain : CodedDeletionTraceTargets.ActualCodedChain := by
 intro R H G M W body alpha Delta trace steps c left right parameter gamma finalLeft finalRight finalParameter finalGamma _length hs ha hsteps hf
 exact rowApply R H G M W trace steps c finalLeft finalRight finalParameter finalGamma
   (allRows R H G M W trace steps c left right parameter gamma hs ha) hsteps hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceProof
