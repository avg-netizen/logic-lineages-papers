module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (headCode tailCode)
open ID1Completion.InternalListCodecDecompositionSupportProof (reconstructNonzero nonzeroRename)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthConsProof (positiveLengthOnCons)
open NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem nonzeroScratch (vertices k : OTerm α)
    (known : Nonempty (Derivation body Γ (memberGraph vertices k))) :
    Nonempty (Derivation body Γ (eqn vertices z).not) := by
  let A := eqn vertices z
  let Δ := A :: Γ
  obtain ⟨hit⟩ := known
  have e : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have bad := headTransport scratchMember (suc z) vertices z ![k] ⟨e⟩ ⟨addHyp hit A⟩
  have impossible := nilRecover memberBase memberStep (suc z) ![k] bad
  obtain ⟨f⟩ := valueUnique memberBase (suc z) z ![k] impossible (zeroConstantValue ![k])
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply f)⟩

private theorem chooseHeadOrTail (p : Program 1) (n : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary p out (n.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  apply programCases p ![n] goal
  intro β j Δ out keep h
  rw [unaryInputsRename] at h
  exact k β j Δ out keep h

private theorem fromHead (vertices head : OTerm α) (goal : Formula α)
    (positive : Nonempty (Derivation body Γ (eqn vertices z).not))
    (h : Nonempty (Derivation body Γ (unary headCode head vertices)))
    (k : PositiveLengthK body Γ vertices goal) : Nonempty (Derivation body Γ goal) := by
  apply chooseHeadOrTail tailCode vertices goal
  intro β i Δ tail keep0 t
  have p := renameInto positive i Δ keep0
  rw [nonzeroRename] at p
  have hh := renameInto h i Δ keep0
  rw [unaryRename] at hh
  have cell := reconstructNonzero (vertices.relabel i) (head.relabel i) tail p hh t
  apply positiveLengthOnCons (vertices.relabel i) (head.relabel i) tail (goal.relabel i) cell
  intro γ j Θ fuel keep1 length
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  exact k γ (j ∘ i) Θ fuel keep (by simpa only [Term.relabel_relabel] using length)

theorem exact_OpenCoverPositiveScratchLength : ExactOpenCoverPositiveScratchLength := by
  intro body α Γ vertices key goal held k
  have positive := nonzeroScratch vertices key held
  apply chooseHeadOrTail headCode vertices goal
  intro β i Δ head keep0 h
  have p := renameInto positive i Δ keep0
  rw [nonzeroRename] at p
  apply fromHead (vertices.relabel i) head (goal.relabel i) p h
  intro γ j Θ fuel keep1 length
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  exact k γ (j ∘ i) Θ fuel keep (by simpa only [Term.relabel_relabel] using length)

#print axioms nonzeroScratch
#print axioms exact_OpenCoverPositiveScratchLength
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthProof
