module
public import LogicLineages.CartierObserverCurrent.MainTheoremBoundaryTargets
public import LogicLineages.CartierObserverCurrent.LinkedBoundaryParityTargets
import LogicLineages.CartierObserverCurrent.FullThetaEntryStatementChecks
import LogicLineages.CartierObserverCurrent.FullOmegaBlockStatementChecks
import LogicLineages.CartierObserverCurrent.LinkedBoundaryParityStatementChecks
import LogicLineages.OrdinalComparison.OmegaBlockPrefixProof
public meta import LogicLineages.Audit

public section
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Boundary
open LogicLineages.OrdinalComparison

/-- Pure arithmetic of the linked entry norm, stated over an abstract
natural so that no decision procedure sees an ordinal or a count. -/
theorem entryArithmetic (u : Nat) (hu : 4 ≤ u) :
    u - 4 + 3 ≤ u ∧ u - (u - 4) - 3 = 1 := by omega

theorem linkedBudgetLarge (u : Nat) : 16 ≤ Phi u ∧ 2 ≤ Phi u := by
  have h : 16 ≤ Phi u := by
    calc
      16 = 2 ^ 4 := by decide
      _ ≤ 2 ^ (u + 100) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ Phi u := two_pow_shift_le_Phi u
  exact ⟨h, le_trans (by decide) h⟩

/-- The head block of total norm four above omega^omega is omega^omega+1. -/
theorem headFour (u : Nat) (hu : 4 ≤ u) :
    actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - (u - 4)) =
      Ordinal.omega0 ^ Ordinal.omega0 + 1 := by
  rw [actualHeadInitial, actualOmegaOmegaFacts.2.2, (entryArithmetic u hu).2, Nat.cast_one]

theorem linkedFirstBlock : Targets.LinkedFirstBlock := by
  intro v hv
  have hu : 4 ≤ Phi v := hv.trans (self_lt_Phi v).le
  have hlarge := linkedBudgetLarge (Phi v)
  have harith := (entryArithmetic (Phi v) hu).1
  have hhead := headFour (Phi v) hu
  have hE := FullThetaEntry.StatementChecks.fixed_completeEntry.2.2 v hv
  have hP := LinkedBoundaryParity.StatementChecks.fixed_actualBoundaryParity v hv
  dsimp only at hE hP ⊢
  obtain ⟨-, hnorm, -, -, -, hstep, hp, hnp, hmin, -⟩ := hE
  have hpar := hP.2.2.2.2.1
  have hblock := FullOmegaBlock.StatementChecks.fixed_completeOmegaBlock.2.2 _ hp hmin (Phi v) 2
    (by rw [hnp]; exact harith) (by decide) hlarge.1 hlarge.2
  dsimp only at hblock
  simp only [hnp] at hblock
  have hstep' := hstep.trans (congrArg (fun t => _ + t) hhead.symm)
  refine ⟨hnorm, hnp, hstep', ?_, ?_, ?_, hpar⟩
  · rw [hstep']
    exact hblock.2.1
  · rw [hstep']
    exact hblock.2.2.1
  · rw [hstep']
    exact hblock.2.2.2.1

/-- Boundary part of item 4 of current20 thm:main: lem:entry,
prop:omega-block, equation (delta) and the first block of the actual descent. -/
theorem boundary :
    FullThetaEntry.Targets.CompleteEntry ∧
    FullOmegaBlock.Targets.CompleteOmegaBlock ∧
    LinkedBoundaryParity.Targets.ActualBoundaryParity ∧
    Targets.LinkedFirstBlock :=
  ⟨FullThetaEntry.StatementChecks.fixed_completeEntry,
    FullOmegaBlock.StatementChecks.fixed_completeOmegaBlock,
    LinkedBoundaryParity.StatementChecks.fixed_actualBoundaryParity,
    linkedFirstBlock⟩

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem.Boundary
end LogicLineages.CartierObserverCurrent.MainTheorem.Boundary
