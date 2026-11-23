module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankPartitionZeroCertificateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenTerminalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothZeroTerminalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven)
open NumberedWindowInternalRankPartitionedAddress (rankPartitionedAddress)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedAddressPositiveOpenProof (AddressAtReport)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof (loopAt)
open NumberedWindowInternalParameterizedPositiveFoldOpenTerminalProof (exact_OpenZeroPositiveTerminal)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalAddressRankZeroRawProof (exact_OpenRawRankFromAddressZero)
open NumberedWindowInternalCompleteRankPartitionZeroCertificateProof (exact_OpenCompleteRankZeroCertificateCases)

private theorem reportRename {α β : Type} (cv tv : Program 1) (P : Program 5)
    (x w y c ty src dst : OTerm α) (ρ : α → β) :
    (AddressAtReport cv tv P x w y c ty src dst).relabel ρ =
      AddressAtReport cv tv P (x.relabel ρ) (w.relabel ρ) (y.relabel ρ)
        (c.relabel ρ) (ty.relabel ρ) (src.relabel ρ) (dst.relabel ρ) := by
  simp only [AddressAtReport,conjunctionRename,addressReportRename,unaryRename,graph5Rename,sucRelabel,zRelabel]

/-- The actual conservative complete-rank body supplies an opened
certificate at genuine zero/zero endpoints. Both original raw classes
have real zero reports; the retained nonempty tape has the genuine
zero-filtered recursor and matching terminal scratch in that body. -/
theorem exact_OpenCompleteRankBothZeroTerminal
    (cv tv g j : Program 1) (W L d : Program 3) (raw : Program 5) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x w y : OTerm α) (goal : Formula α) :
    let i := addressScalar cv tv W L
    let R := completeRankEven i (addressRank g) (rankPartitionedAddress cv tv g raw L)
    let S := data i j R d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (unary (addressRank g) z x)) →
    Nonempty (Derivation B Γ (unary (addressRank g) z y)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (ctx ty src dst state : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Nonempty (Derivation B Δ (AddressAtReport cv tv (zeroPositive g raw L)
        (x.relabel ρ) (w.relabel ρ) (y.relabel ρ) ctx ty src dst)) →
      Nonempty (Derivation B Δ (unary g z src)) →
      Nonempty (Derivation B Δ (unary g z dst)) →
      Nonempty (Derivation B Δ (eqn (w.relabel ρ) z).not) →
      Nonempty (Derivation B Δ (loopAt (zeroOutput g (advance raw L)) state (w.relabel ρ) ctx ty
        (suc src) (w.relabel ρ))) →
      Nonempty (Derivation B Δ (scratchGraph state z (suc dst))) →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal) := by
  intro i R S B accepted rx ry next
  apply exact_OpenCompleteRankZeroCertificateCases cv tv g j W L d raw c α Γ x w y goal accepted ry
  intro β ρ Δ ctx ty src dst keep report
  obtain ⟨rep⟩ := report
  let left := Derivation.conjunctionLeft rep
  let right := Derivation.conjunctionLeft (Derivation.conjunctionRight rep)
  let tail := Derivation.conjunctionRight (Derivation.conjunctionRight rep)
  have sx := renameInto rx ρ Δ keep
  have sy := renameInto ry ρ Δ keep
  rw [unaryRename,zRelabel] at sx sy
  have zx := exact_OpenRawRankFromAddressZero g (x.relabel ρ) src ⟨Derivation.conjunctionLeft left⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight left))⟩ sx
  have zy := exact_OpenRawRankFromAddressZero g (y.relabel ρ) dst ⟨Derivation.conjunctionLeft right⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight right))⟩ sy
  apply exact_OpenZeroPositiveTerminal g raw L ctx ty src (w.relabel ρ) dst (goal.relabel ρ)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight tail)⟩
  intro γ ι Θ state keeps nz loop scratch
  have report' := renameInto ⟨rep⟩ ι Θ keeps
  have zx' := renameInto zx ι Θ keeps
  have zy' := renameInto zy ι Θ keeps
  rw [unaryRename,zRelabel] at zx' zy'
  simp only [reportRename,Term.relabel_relabel] at report'
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (ι ∘ ρ) ∈ Θ := by
    rw [← formulaRelabelComposition ρ ι f]
    exact keeps _ (keep f hf)
  rw [formulaRelabelComposition ρ ι goal]
  exact next γ (ι ∘ ρ) Θ (ctx.relabel ι) (ty.relabel ι) (src.relabel ι) (dst.relabel ι)
    state both report' zx' zy' (by simpa only [Term.relabel_relabel] using nz)
    (by simpa only [Term.relabel_relabel] using loop) scratch

#print axioms exact_OpenCompleteRankBothZeroTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothZeroTerminalProof
