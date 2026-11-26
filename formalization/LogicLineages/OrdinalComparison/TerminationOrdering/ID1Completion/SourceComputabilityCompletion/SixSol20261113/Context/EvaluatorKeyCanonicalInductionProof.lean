module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof EvaluatorKeyCanonicalBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem payloadStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q : OTerm alpha) (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q))) :
 Nonempty (Derivation body Delta (atPayload p H G W P q)) := by
 apply atPayloadIntro p H G W P q
 let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let leftOut : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let rightOut : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let Theta := Premises p H G W P left right leftOut rightOut parameter ::
   graph1 InternalUnpair.right (q.relabel Sum.inl) left :: Delta.map (fun f => f.relabel Sum.inl)
 have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 5) Theta (by
   intro f hf
   exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)))
 rw [belowPayloadRename] at hb'
 obtain ⟨h⟩ := EvaluatorKeyCanonicalStepProof.actualStep p H G W P body (alpha ⊕ Fin 5) Theta
   (q.relabel Sum.inl) left right leftOut rightOut parameter hb'
   (show Nonempty (Derivation body Theta (graph1 InternalUnpair.right (q.relabel Sum.inl) left)) from
     ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
   (show Nonempty (Derivation body Theta (Premises p H G W P left right leftOut rightOut parameter)) from
     ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
theorem actualAll : EvaluatorKeyCanonicalInductionTargets.ActualAll := by
 intro p H G W P body alpha Delta payload
 apply payloadInduction p H G W P payload
 intro beta Theta q hb
 exact payloadStep p H G W P q hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionProof
