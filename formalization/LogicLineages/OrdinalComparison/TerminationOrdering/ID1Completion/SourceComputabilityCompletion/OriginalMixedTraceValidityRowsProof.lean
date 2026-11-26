module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedTraceValidityDefinitions
open OriginalMixedTraceValiditySyntaxProof
open OriginalMixedTraceValidityBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Generic internal strong-path induction assembly. No native finite fuel;
all four runtime coordinates remain bound inside each row. -/
theorem rowsFromCore (source : Program 2) (leaf : Program 4)
 (core : ∀ (beta : Type) (Theta : List (Formula beta))
  (path s t cert oldParam         : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath source leaf path)) →
  Nonempty (Derivation body Theta (fields source leaf path s t cert oldParam        )) →
  Nonempty (Derivation body Theta (result source leaf t oldParam)))
 (path : OTerm alpha) : Nonempty (Derivation body Delta (AtPath source leaf path)) := by
 apply pathInduction source leaf path
 intro beta Theta code hi
 apply atPathIntro
 unfold matrix
 let A : Formula (beta ⊕ Fin 4) := fields source leaf (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
 let Xi := A :: Theta.map (fun q => q.relabel Sum.inl)
 have hf : Nonempty (Derivation body Xi A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hi' := renameInto hi (Sum.inl : beta → beta ⊕ Fin 4) Xi
  (by intro f h; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
 rw [belowPathRename] at hi'
 obtain ⟨r⟩ := core (beta ⊕ Fin 4) Xi (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) hi' hf
 exact ⟨Derivation.implicationIntroduction r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityRowsProof
