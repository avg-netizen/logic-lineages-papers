module
public import LogicLineages.PermittedControl.SignedRowGuardedTestTargets
import LogicLineages.PermittedControl.SignedRowSliceValueStatementChecks
import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceReadProof
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowGuardedTest
open SignedRowSliceValue (valueAt)
open StatementChecks (fixed_signedRowSliceExactValueAtHit fixed_signedRowCoordinateSliceFailureExact)

theorem exactValue : ExactValue := by
  intro f ρ rank a c terms agree value
  constructor
  · rintro ⟨values,reads,sum⟩
    obtain ⟨b,residual,hit⟩ :=
      SignedCongruenceMatrixSlice.sliceExists f ρ rank a c terms values reads agree
    have same := fixed_signedRowSliceExactValueAtHit f ρ rank a c terms b residual agree hit value
    exact ⟨b,residual,hit,same.mp ⟨values,reads,sum⟩⟩
  · rintro ⟨b,residual,hit,actual⟩
    exact (fixed_signedRowSliceExactValueAtHit f ρ rank a c terms b residual agree hit value).mpr actual

theorem exactSelectedFailures : ExactSelectedFailures := by
  intro f ρ rank a c terms agree
  have statuses := fixed_signedRowCoordinateSliceFailureExact f rank a c terms
  constructor
  · intro invalid
    refine ⟨statuses.1.mp invalid,?_⟩
    intro value actual
    obtain ⟨_,_,hit,_⟩ := (exactValue f ρ rank a c terms agree value).mp actual
    simp [invalid] at hit
  · intro miss
    refine ⟨statuses.2.mp miss,?_⟩
    intro value actual
    obtain ⟨_,_,hit,_⟩ := (exactValue f ρ rank a c terms agree value).mp actual
    simp [miss] at hit

end LogicLineages.PermittedControl.SignedRowGuardedTest
