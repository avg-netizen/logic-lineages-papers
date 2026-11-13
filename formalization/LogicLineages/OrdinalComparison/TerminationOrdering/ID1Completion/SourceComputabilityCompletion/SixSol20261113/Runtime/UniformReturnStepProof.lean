module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Binder introduction for an independently established original return rule.
This helper does not assert that source admission supplies that rule. -/
theorem frameFromReturn (R : Program 2) (frame payload produced value : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (suffix old work results input pushed output : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
     (geometry (frame.relabel j) (produced.relabel j) (value.relabel j)
       suffix old work results input pushed output)) →
   Nonempty (Derivation body Theta (graph1 (OriginalHereditaryReturnStep.step R) output input))) :
 Nonempty (Derivation body Delta (Framed R frame produced value)) := by
 unfold Framed
 apply actualFiniteUniversalIntroduction body alpha 7 Delta
 unfold frameBody
 let suffix : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
 let old : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
 let work : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
 let results : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
 let input : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
 let pushed : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
 let output : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
 let A := geometry (frame.relabel Sum.inl) (produced.relabel Sum.inl) (value.relabel Sum.inl)
   suffix old work results input pushed output
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 7))
 have hi : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 7) ∈ Theta :=
   fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
 have hg : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have ht := next (alpha ⊕ Fin 7) Sum.inl Theta suffix old work results input pushed output hi hg
 have hf' := renameInto hf Sum.inl Theta hi
 simp only [graph2Rename,numeralRename] at hf'
 have hc := OriginalInternalReturnCombinedControlProof.control R input work results
   (frame.relabel Sum.inl) suffix (payload.relabel Sum.inl)
   output (andLeft (andRight (andRight hg))) (andLeft hg) hf' ht
 obtain ⟨hr⟩ := InternalNumericIterationProof.frontSuccBackward
   (OriginalHereditaryCombinedStep.step R) (numeral 0) output input output hc
   (InternalNumericIterationSupportProof.repeatZeroValue (OriginalHereditaryCombinedStep.step R) output)
 exact ⟨Derivation.implicationIntroduction hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStepProof
