module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLow
open HeterogeneousSignedMatrixSlice (Snapshot)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows accepts exactPlainTerminalSuffix)

theorem exactPrintedPlainInfiniteLow : ExactPrintedPlainInfiniteLow := by
  intro f ρ known gates p plain rank bound _ prior positive
  let gs := circuit known gates p
  let pass : (Nat → Nat) → Snapshot → Prop := fun θ snap =>
    ∃ values : Snapshot, snap = passingList θ gs ++ values ∧ accepts p positive values
  have combined (θ : Nat → Nat) (values : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p)
      (passingList θ gs) values (exactNormalizedCircuitRows f θ gs).1
  have low := HeterogeneousSignedMatrixLowStrips.exactGuardedLowExistential
    f ρ prior rank bound (matrix known gates p) pass true
  constructor
  · rintro ⟨a,within,priorAt,graph,polarity⟩
    let θ := Function.update ρ rank a
    obtain ⟨values,actual,accepted⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp polarity
    have hRows := (combined θ values).mpr ⟨(exactNormalizedCircuitRows f θ gs).2.mpr graph,actual⟩
    obtain ⟨branch,residual,member,hit,prior',snap,hSnap,hPass⟩ :=
      low.mp ⟨a,within,priorAt,_,hRows,⟨values,rfl,accepted⟩⟩
    obtain ⟨vs,rfl,yes⟩ := hPass
    exact ⟨branch,residual,member,hit,prior',vs,hSnap,yes⟩
  · rintro ⟨branch,residual,member,hit,priorAt,values,actual,accepted⟩
    obtain ⟨a,within,prior',snap,hSnap,hPass⟩ :=
      low.mpr ⟨branch,residual,member,hit,priorAt,_,actual,⟨values,rfl,accepted⟩⟩
    let θ := Function.update ρ rank a
    obtain ⟨vs,rfl,yes⟩ := hPass
    obtain ⟨graph,suffix⟩ := (combined θ vs).mp hSnap
    exact ⟨a,within,prior',(exactNormalizedCircuitRows f θ gs).2.mp graph,
      (exactPlainTerminalSuffix f θ p plain positive).mpr ⟨vs,suffix,yes⟩⟩

theorem exactPrintedPlainResidualOperands : ExactPrintedPlainResidualOperands := by
  intro f known gates p rank a residual hit
  exact HeterogeneousSignedMatrixSlice.residualRowsExact f rank a
    (matrix known gates p) residual hit

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLow
