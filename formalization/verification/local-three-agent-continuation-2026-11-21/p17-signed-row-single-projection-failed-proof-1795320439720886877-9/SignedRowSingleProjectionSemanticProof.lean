module
public import LogicLineages.PermittedControl.SignedRowSingleProjectionTargets
import LogicLineages.PermittedControl.HighTailNamedRowProjectionStatementChecks
import LogicLineages.PermittedControl.SignedRowLowStripsStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSingleProjection
open HighTailNamedRowProjection (coordinateTail)
open SignedRowCoordinateSlice (denotes)
open StatementChecks (fixed_signedRowGuardedLowStrips fixed_actualHighTailNamedRowProjection)

theorem actualCaseSplit : ActualCaseSplit := by
  intro f B hf m name rank c terms ρ ν positive selected proper others tied
  have low : (∃ z : Nat, z < coordinateTail B m terms ∧
      denotes f (Function.update ρ rank z) m c terms) ↔ LowHit f ρ B m rank c terms := by
    simpa only [LowHit,true_and] using fixed_signedRowGuardedLowStrips
      f ρ (fun _ => True) rank (coordinateTail B m terms) m c terms positive
  have high := fixed_actualHighTailNamedRowProjection
    f B hf m name rank c terms ρ ν positive selected proper others tied
  constructor
  · rintro ⟨z,holds⟩
    rcases Nat.lt_or_ge z (coordinateTail B m terms) with below | above
    · exact Or.inl (low.mp ⟨z,below,holds⟩)
    · exact Or.inr (high.mpr ⟨z,above,holds⟩)
  · rintro (below | above)
    · obtain ⟨z,_,holds⟩ := low.mpr below
      exact ⟨z,holds⟩
    · obtain ⟨z,_,holds⟩ := high.mp above
      exact ⟨z,holds⟩

end LogicLineages.PermittedControl.SignedRowSingleProjection
