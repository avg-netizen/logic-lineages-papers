module
public import LogicLineages.PermittedControl.AffineCollapsePairListLowTargets
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapsePairListLow
open HeterogeneousSignedMatrixSlice (Snapshot actualRows)
open AffineCollapseGuardedLow (OriginalTestAt)

theorem exactFiniteListLow : ExactFiniteListLow := by
  intro f ρ prior pairs hlim rank bound testRows test positive
  let pass : (Nat → Nat) → Snapshot → Prop := fun θ values =>
    ∃ testValues : Snapshot, values = prefixSnapshot θ pairs ++ testValues ∧
      OriginalTestAt test positive θ testValues
  have low := HeterogeneousSignedMatrixLowStrips.exactGuardedLowExistential
    f ρ prior rank bound (prefixRows pairs ++ testRows) pass true
  constructor
  · rintro ⟨a,within,pr,graph,values,actual,holds⟩
    let θ := Function.update ρ rank a
    have hGuard := (exactSharedPrefix f θ pairs hlim).mpr graph
    have hRows := (actualRowsAppend f θ (prefixRows pairs) testRows _ values
      (prefixLength θ pairs)).mpr ⟨hGuard,actual⟩
    obtain ⟨branch,residual,member,hit,pr',snapshot,hSnap,hPass⟩ :=
      low.mp ⟨a,within,pr,_,hRows,⟨values,rfl,holds⟩⟩
    obtain ⟨values',rfl,hHolds⟩ := hPass
    exact ⟨branch,residual,member,hit,pr',values',hSnap,hHolds⟩
  · rintro ⟨branch,residual,member,hit,pr,values,actual,holds⟩
    obtain ⟨a,within,pr',snap,hSnap,hPass⟩ :=
      low.mpr ⟨branch,residual,member,hit,pr,_,actual,⟨values,rfl,holds⟩⟩
    let θ := Function.update ρ rank a
    obtain ⟨values',rfl,hHolds⟩ := hPass
    obtain ⟨hGuard,hTest⟩ := (actualRowsAppend f θ (prefixRows pairs) testRows _ values'
      (prefixLength θ pairs)).mp hSnap
    exact ⟨a,within,pr',(exactSharedPrefix f θ pairs hlim).mp hGuard,values',hTest,hHolds⟩

end LogicLineages.PermittedControl.AffineCollapsePairListLow
