module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadFinishProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenTerminalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecDecompositionSupportProof (nonzeroRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof (loopAt)
open NumberedWindowInternalParameterizedPositiveFoldOpenReadProof (exact_OpenParameterizedPositiveToFinish)
open NumberedWindowInternalParameterizedPositiveFoldOpenReadFinishProof (exact_OpenParameterizedReadFinish)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual parameterized checker exposes the real chosen loop
result at the certificate's own fuel. In the same arbitrary open
body, its cursor is zero and its current is exactly the successful target. -/
theorem exact_OpenParameterizedPositiveTerminal (A : Program 4)
    (c ty src cert dst : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ
      (programGraph (positiveAt A) (suc z) (args5 c ty src cert dst))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (eqn (cert.relabel j) z).not) →
      Nonempty (Derivation B Δ (loopAt A state (cert.relabel j) (c.relabel j) (ty.relabel j)
        (suc (src.relabel j)) (cert.relabel j))) →
      Nonempty (Derivation B Δ (scratchGraph state z (suc (dst.relabel j)))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  obtain ⟨read⟩ := exact_OpenParameterizedPositiveToFinish A c ty src cert dst held
  apply exact_OpenParameterizedReadFinish A c ty (suc src) cert dst goal
    ⟨Derivation.conjunctionRight read⟩
  intro β j Δ state keep loop scratch
  have nz := renameInto ⟨Derivation.conjunctionLeft read⟩ j Δ keep
  rw [nonzeroRename] at nz
  rw [sucRelabel] at loop
  exact next β j Δ state keep nz loop scratch

theorem exact_OpenZeroPositiveTerminal (g : Program 1) (raw : Program 5) (L : Program 3)
    (c ty src cert dst : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ
      (programGraph (zeroPositive g raw L) (suc z) (args5 c ty src cert dst))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (eqn (cert.relabel j) z).not) →
      Nonempty (Derivation B Δ (loopAt (zeroOutput g (advance raw L)) state (cert.relabel j)
        (c.relabel j) (ty.relabel j) (suc (src.relabel j)) (cert.relabel j))) →
      Nonempty (Derivation B Δ (scratchGraph state z (suc (dst.relabel j)))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) :=
  exact_OpenParameterizedPositiveTerminal (zeroOutput g (advance raw L)) c ty src cert dst goal held next

#print axioms exact_OpenParameterizedPositiveTerminal
#print axioms exact_OpenZeroPositiveTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenTerminalProof
