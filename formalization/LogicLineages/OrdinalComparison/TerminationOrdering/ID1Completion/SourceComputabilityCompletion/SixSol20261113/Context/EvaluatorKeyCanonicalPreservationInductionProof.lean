module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyCanonicalPreservationInductionDefinitions EvaluatorKeyCanonicalPreservationSyntaxProof EvaluatorKeyCanonicalPreservationBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem payloadStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W)
 (q : OTerm alpha) (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q))) :
 Nonempty (Derivation body Delta (atPayload p H G W P q)) := by
 apply atPayloadIntro p H G W P q
 let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let Theta := Premises p H G W P input out parameter ::
   graph1 InternalUnpair.right (q.relabel Sum.inl) input :: Delta.map (fun f => f.relabel Sum.inl)
 have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 3) Theta (by
   intro f hf
   exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)))
 rw [belowPayloadRename] at hb'
 obtain ⟨h⟩ := EvaluatorKeyCanonicalPreservationStepProof.actualStep p H G W P compat
   (q.relabel Sum.inl) input out parameter hb'
   (show Nonempty (Derivation body Theta (graph1 InternalUnpair.right (q.relabel Sum.inl) input)) from
     ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
   (show Nonempty (Derivation body Theta (Premises p H G W P input out parameter)) from
     ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
theorem actualAll : EvaluatorKeyCanonicalPreservationInductionTargets.ActualAll := by
 intro p H G W P compat body alpha Delta payload
 apply payloadInduction p H G W P payload
 intro beta Theta q hb
 exact payloadStep p H G W P compat q hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionProof
