module

public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsInverseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankSelectedAdvanceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFoldOpenConsInverseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalParameterizedPositiveFold (stepAt)
open NumberedWindowInternalParameterizedPositiveFoldOpenConsInverseProof
  (exact_OpenParameterizedConsTransitionInverse)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalZeroRankSelectedAdvanceProof (exact_OpenZeroRankSelectedAdvanceBoth)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual one visible zero-fold cell. The held positive before/after
encoded states, rather than their numerals, expose the original selected
raw q,w,r and both true zero reports. -/
theorem exact_OpenZeroRankFoldConsInverse
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (out k prior c ty start cert cursor current hop tail target : OTerm α)
    (goal : Formula α)
    (before : Nonempty (Derivation B Γ (scratchGraph prior cursor (suc current))))
    (owner : Nonempty (Derivation B Γ (consGraph cursor hop tail)))
    (after : Nonempty (Derivation B Γ (scratchGraph out tail (suc target))))
    (sourceZero : Nonempty (Derivation B Γ (unary g z current)))
    (held : Nonempty (Derivation B Γ
      (programGraph (stepAt (zeroOutput g (advance raw (checkedLeast g L))))
        out (call6 k prior c ty start cert))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (hopCalls raw L (c.relabel j) (ty.relabel j) (current.relabel j)
        (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation B Δ (unary g z q)) →
      Nonempty (Derivation B Δ (unary g z r)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let A := zeroOutput g (advance raw (checkedLeast g L))
  have cell := exact_OpenParameterizedConsTransitionInverse A out k prior c ty start cert cursor
    (suc current) hop tail (suc target) before owner after held
  exact exact_OpenZeroRankSelectedAdvanceBoth g raw L c ty current hop target goal sourceZero cell next

#print axioms exact_OpenZeroRankFoldConsInverse
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFoldOpenConsInverseProof
