module
public import LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal
open OriginalPrintedCircuitTerminal (observe)

theorem exactDefinedDomainCounterexample : ExactDefinedDomainCounterexample := by
  intro f gates p polarity
  constructor
  · intro none base domain
    obtain ⟨bit,done⟩ := domain
    by_cases same : bit = polarity
    · rw [same] at done
      exact done
    · have contrary : bit = !polarity := by cases bit <;> cases polarity <;> simp_all
      rw [contrary] at done
      exact False.elim (none ⟨base,done⟩)
  · rintro all ⟨base,contrary⟩
    have same := all base ⟨!polarity,contrary⟩
    have bit : (!polarity) = polarity := Except.ok.inj (contrary.symm.trans same)
    cases polarity <;> cases bit

end LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal
