module
public import LogicLineages.PermittedControl.OriginalFieldGateInfiniteStripTargets
import LogicLineages.PermittedControl.OriginalFieldGateMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalFieldGateInfiniteStrip
open OriginalNaturalFieldGates (Valuation)
open HeterogeneousSignedMatrixSlice (Snapshot)
open OriginalFieldGateMatrix (rowsList passingList exactOriginalFieldList)

theorem exactFieldGateInfiniteStrips : ExactFieldGateInfiniteStrips := by
  intro f ρ rank bound gates testRows prior test positive
  let pass : Valuation → Snapshot → Prop := fun θ snap =>
    ∃ values : Snapshot, snap = passingList θ gates ++ values ∧
      (if positive then test θ values else ¬ test θ values)
  have combined (θ : Valuation) (values : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gates) testRows
      (passingList θ gates) values (exactOriginalFieldList f θ gates).1
  have low := HeterogeneousSignedMatrixLowStrips.exactGuardedLowExistential
    f ρ prior rank bound (rowsList gates ++ testRows) pass true
  constructor
  · rintro ⟨a,within,priorAt,graphs,vals,actual,holds⟩
    let θ := Function.update ρ rank a
    have hGate := (exactOriginalFieldList f θ gates).2.mpr graphs
    have hRows := (combined θ vals).mpr ⟨hGate,actual⟩
    obtain ⟨branch,residual,member,hit,prior',snap,hSnap,hPass⟩ :=
      low.mp ⟨a,within,priorAt,_,hRows,⟨vals,rfl,holds⟩⟩
    obtain ⟨values,rfl,accepted⟩ := hPass
    exact ⟨branch,residual,member,hit,prior',values,hSnap,accepted⟩
  · rintro ⟨branch,residual,member,hit,priorAt,vals,actual,holds⟩
    obtain ⟨a,within,prior',snap,hSnap,hPass⟩ :=
      low.mpr ⟨branch,residual,member,hit,priorAt,_,actual,⟨vals,rfl,holds⟩⟩
    let θ := Function.update ρ rank a
    obtain ⟨values,rfl,accepted⟩ := hPass
    obtain ⟨hGate,hTest⟩ := (combined θ values).mp hSnap
    exact ⟨a,within,prior',(exactOriginalFieldList f θ gates).2.mp hGate,values,hTest,accepted⟩

theorem exactFieldGateResidualOperands : ExactFieldGateResidualOperands := by
  intro f rank a gates testRows residual hit
  exact HeterogeneousSignedMatrixSlice.residualRowsExact f rank a
    (rowsList gates ++ testRows) residual hit

end LogicLineages.PermittedControl.OriginalFieldGateInfiniteStrip
