module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalDirectBoundaryGuardsTargets (scalarFailures typedScratch)
open NumberedWindowInternalDirectTypedScratchReportTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem sources (i : Program 1) (code mapped : OTerm α)
    (mapHeld : Nonempty (Derivation B Γ (unary (normalizedMap i) mapped code))) :
    ∀ k : Fin 2, Nonempty (Derivation B Γ
      (programGraph ((![normalizedMap i,constantZero 1] : Fin 2 → Program 1) k)
        ((![mapped,z] : Fin 2 → OTerm α) k) ![code])) := by
  intro k
  refine Fin.cases ?_ (fun q => ?_) k
  · exact mapHeld
  · obtain rfl := Fin.eq_zero q
    exact constantZeroValue ![code]

private theorem keepUnary {β : Type} (p : Program 1) (code : OTerm α)
    (ρ : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ)
    (held : Nonempty (Derivation B Γ (unary p (suc z) code))) :
    Nonempty (Derivation B Δ (unary p (suc z) (code.relabel ρ))) := by
  simpa only [unaryRename,sucRelabel,zRelabel] using renameInto held ρ Δ keep

theorem exact_EliminateTypedScratch : ExactEliminateTypedScratch := by
  intro i B α Γ code goal held next
  apply optionGraphCases (scalarFailures i) ![code] goal
  · intro β ρ Δ keep clean
    rw [inputsRename] at clean
    apply programCases (normalizedMap i) ![code.relabel ρ] (goal.relabel ρ)
    intro γ τ Ω mapped retain hasMap
    rw [inputsRename] at hasMap
    have preserved : Nonempty (Derivation B Ω
      (programGraph (scalarFailures i) z ![code.relabel (τ ∘ ρ)])) := by
      simpa only [programRename,inputsRename,zRelabel,Term.relabel_relabel] using
        renameInto clean τ Ω retain
    have actual : Nonempty (Derivation B Ω
      (unary (normalizedMap i) mapped (code.relabel (τ ∘ ρ)))) := by
      simpa only [unary,Term.relabel_relabel] using hasMap
    have hm : Nonempty (Derivation B Ω (programGraph scratchMember z ![mapped,z])) :=
      compositionRecover scratchMember ![normalizedMap i,constantZero 1] z ![code.relabel (τ ∘ ρ)]
        ![mapped,z] preserved (sources i (code.relabel (τ ∘ ρ)) mapped actual)
    rw [formulaRelabelComposition]
    exact next γ (τ ∘ ρ) Ω mapped (keepThrough ρ τ keep retain) ⟨actual,hm⟩
  · intro β ρ Δ predecessor keep hit
    rw [inputsRename] at hit
    let xs := ![code.relabel ρ]
    have denied := successorBranchElim (scalarFailures i) (constantOne 1) (constantZero 1)
      (suc z) predecessor xs hit (keepUnary (typedScratch i) code ρ Δ keep held)
    obtain ⟨e⟩ := valueUnique (constantZero 1) (suc z) z xs denied (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

theorem exact_IntroduceTypedScratch : ExactIntroduceTypedScratch := by
  intro i B α Γ code mapped h
  apply zeroBranchIntro (scalarFailures i) (constantOne 1) (constantZero 1)
    (suc z) ![code] _ (oneConstantValue ![code])
  exact compositionValue scratchMember ![normalizedMap i,constantZero 1] z ![code]
    ![mapped,z] h.missingZero (sources i code mapped h.mappedCall)

#print axioms exact_EliminateTypedScratch
#print axioms exact_IntroduceTypedScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportProof
