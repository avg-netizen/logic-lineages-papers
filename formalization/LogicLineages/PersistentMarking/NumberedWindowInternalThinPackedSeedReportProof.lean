module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedPairState
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSeedReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalThinPackedPairState

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Choose the actual original cover and members outputs at a genuine
held least, without imposing any equality of different raw seeds. -/
theorem exact_OpenThinPackedSeedReport (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed least : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (leastGraph C X W s ctx ty seed least)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices pool : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (seedReport C X W s (ctx.relabel j) (ty.relabel j)
        (seed.relabel j) vertices pool (least.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases (scratchVertices C s) ![seed] goal
  intro β j Δ verts keep cover
  rw [unaryInputsRename] at cover
  have min := renameInto held j Δ keep
  rw [leastRename] at min
  apply programCases (membersAtSeed C X W s) ![ctx.relabel j,ty.relabel j,seed.relabel j] (goal.relabel j)
  intro γ k Θ pool keep' chosen
  rw [tripleInputsRename] at chosen
  have l := renameInto min k Θ keep'
  have r := renameInto (phi := NumberedWindowInternalSparsePathEnvelopeTargets.unary (scratchVertices C s) verts (seed.relabel j)) cover k Θ keep'
  simp only [leastRename,Term.relabel_relabel] at l
  simp only [unaryRename,Term.relabel_relabel] at r
  simp only [Term.relabel_relabel] at chosen
  have together (f : Formula α) (mem : f ∈ Γ) : f.relabel (k ∘ j) ∈ Θ := by
    rw [← formulaRelabelComposition j k f]
    exact keep' _ (keep f mem)
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := r
  obtain ⟨p⟩ := chosen
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Θ (verts.relabel k) pool together
    ⟨Derivation.conjunctionIntroduction l (Derivation.conjunctionIntroduction r p)⟩

#print axioms exact_OpenThinPackedSeedReport
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSeedReportProof
