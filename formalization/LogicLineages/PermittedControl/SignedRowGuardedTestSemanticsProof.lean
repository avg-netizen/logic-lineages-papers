module
public import LogicLineages.PermittedControl.SignedRowGuardedTestTargets
import LogicLineages.PermittedControl.SignedRowGuardedTestValueProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowGuardedTest

theorem exactGuardedTests : ExactGuardedTests := by
  intro f ρ rank a c terms agree test positive
  constructor
  · rintro ⟨admitted,value,actual,holds⟩
    exact ⟨admitted,value,(exactValue f ρ rank a c terms agree value).mp actual,holds⟩
  · rintro ⟨admitted,value,actual,holds⟩
    exact ⟨admitted,value,(exactValue f ρ rank a c terms agree value).mpr actual,holds⟩

theorem zeroModulusExcluded : ZeroModulusExcluded := by
  intro f ρ rank a c terms positive
  exact ⟨fun h => (Nat.lt_irrefl 0) h.1,fun h => (Nat.lt_irrefl 0) h.1⟩

end LogicLineages.PermittedControl.SignedRowGuardedTest
