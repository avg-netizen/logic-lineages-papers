module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTraceInductionDefinitions
open OriginalMixedDirectBottomTraceInductionSyntaxProof
open OriginalMixedDirectBottomTraceInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Generic internal strong-path induction assembly. No native finite fuel;
all twelve runtime coordinates remain bound inside each row. -/
theorem rowsFromCore (source : Program 2) (leaf : Program 4)
 (core : ∀ (beta : Type) (Theta : List (Formula beta))
  (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath source leaf path)) →
  Nonempty (Derivation body Theta (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
  Nonempty (Derivation body Theta (result source leaf s t newParam erasedS erasedT)))
 (path : OTerm alpha) : Nonempty (Derivation body Delta (AtPath source leaf path)) := by
 apply pathInduction source leaf path
 intro beta Theta code hi
 apply atPathIntro
 unfold matrix
 let A : Formula (beta ⊕ Fin 12) := fields source leaf (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11))
 let Xi := A :: Theta.map (fun q => q.relabel Sum.inl)
 have hf : Nonempty (Derivation body Xi A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hi' := renameInto hi (Sum.inl : beta → beta ⊕ Fin 12) Xi
  (by intro f h; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
 rw [belowPathRename] at hi'
 obtain ⟨r⟩ := core (beta ⊕ Fin 12) Xi (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11)) hi' hf
 exact ⟨Derivation.implicationIntroduction r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionRowsProof
