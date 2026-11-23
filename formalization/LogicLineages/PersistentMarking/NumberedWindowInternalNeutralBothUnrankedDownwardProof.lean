module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankedNeutralTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankAccessibilityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalSuccessorClosure)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalNeutralBothUnrankedDownwardTargets
open NumberedWindowInternalNeutralBothUnrankedDownwardCoreProof
  (formulaRename edgeRename exact_OpenBothUnrankedDownwardArrow)
open NumberedWindowInternalNeutralRankTargets (RankDrop positiveRank)
open NumberedWindowInternalNeutralRankAccessibilityProof (exact_OpenRankAccessibility)
open NumberedWindowInternalNeutralBothUnrankedPullbackTargets (EdgeTargetCarriers)
open NumberedWindowInternalRankedNeutralTypeProof
  (RankedNeutralApplication exact_RankedNeutralComputability)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)

private theorem positiveCannotReachZero
    {S : Data} {g : Program 1} {c : Nat} (drop : RankDrop S g c)
    {α : Type} {Γ : List (Formula α)} (f f' k : OTerm α) (goal : Formula α)
    (e : Nonempty (Derivation (sourceBody S c) Γ (edge S false c f f')))
    (positive : Nonempty (Derivation (sourceBody S c) Γ (positiveRank g k f)))
    (zero : Nonempty (Derivation (sourceBody S c) Γ (unary g z f'))) :
    Nonempty (Derivation (sourceBody S c) Γ goal) := by
  apply drop α Γ k f f' goal e positive
  intro β j Δ m keeps _ target _
  have zero' := renameInto zero j Δ keeps
  rw [unaryRename,zRelabel] at zero'
  obtain ⟨impossible⟩ := valueUnique g (suc m) z ![f'.relabel j] target zero'
  exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

/-- Original C downwards on this same body, with actual lower-codomain
recursion only for the genuine zero/zero matching case. -/
theorem exact_BothUnrankedComputabilityDownward (S : Data) (g : Program 1) (p : Program 3) (c : Nat)
    (drop : RankDrop S g c) (targets : EdgeTargetCarriers S c)
    (rankedApp : RankedNeutralApplication S g p c)
    (matchEdge : BothUnrankedApplicationEdgeMatching S g p c) :
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (f f' : OTerm α),
      Nonempty (Derivation (sourceBody S c) Γ (formula p τ f)) →
      Nonempty (Derivation (sourceBody S c) Γ (edge S false c f f')) →
      Nonempty (Derivation (sourceBody S c) Γ (formula p τ f')) := by
  intro τ
  induction τ with
  | ground =>
    intro α Γ f f' hf e
    exact actualOriginalSuccessorClosure S false c α Γ f f' hf e
  | arrow σ τ _ ih =>
    intro α Γ f f' hf e
    let B := sourceBody S c
    let Q := formula p (.arrow σ τ) f'
    apply optionGraphCases g (![f'] : Fin 1 → OTerm α) Q
    · intro β j Δ keeps targetZero
      rw [unaryInputsRename] at targetZero
      let u := f.relabel j
      let v := f'.relabel j
      have earlier := renameInto hf j Δ keeps
      rw [formulaRename] at earlier
      have nextEdge := renameInto e j Δ keeps
      rw [edgeRename] at nextEdge
      change Nonempty (Derivation B Δ ((formula p (.arrow σ τ) f').relabel j))
      rw [formulaRename]
      apply optionGraphCases g (![u] : Fin 1 → OTerm β) (formula p (.arrow σ τ) v)
      · intro γ η Ω keeps₂ sourceZero
        rw [unaryInputsRename] at sourceZero
        rw [formulaRename]
        have ft := renameInto earlier η Ω keeps₂
        rw [formulaRename] at ft
        have et := renameInto nextEdge η Ω keeps₂
        rw [edgeRename] at et
        have zt := renameInto targetZero η Ω keeps₂
        change Nonempty (Derivation B Ω ((unary g z v).relabel η)) at zt
        rw [unaryRename,zRelabel] at zt
        exact exact_OpenBothUnrankedDownwardArrow S g p c σ τ matchEdge ih
          γ Ω (u.relabel η) (v.relabel η) ft et sourceZero zt
      · intro γ η Ω k keeps₂ sourceRank
        rw [unaryInputsRename] at sourceRank
        have et := renameInto nextEdge η Ω keeps₂
        rw [edgeRename] at et
        have zt := renameInto targetZero η Ω keeps₂
        change Nonempty (Derivation B Ω ((unary g z v).relabel η)) at zt
        rw [unaryRename,zRelabel] at zt
        exact positiveCannotReachZero drop (u.relabel η) (v.relabel η) k _ et sourceRank zt
    · intro β j Δ k keeps targetRank
      rw [unaryInputsRename] at targetRank
      change Nonempty (Derivation B Δ ((formula p (.arrow σ τ) f').relabel j))
      rw [formulaRename]
      have cy := renameInto (targets α Γ f f' e) j Δ keeps
      rw [NumberedWindowInternalFreshProbeAlignmentSyntaxProof.carrierRename] at cy
      exact exact_RankedNeutralComputability S g p c
        (fun _ _ m q ranked carried => exact_OpenRankAccessibility drop m q carried ranked)
        rankedApp (.arrow σ τ) β Δ k (f'.relabel j) targetRank cy

#print axioms exact_BothUnrankedComputabilityDownward
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardProof
