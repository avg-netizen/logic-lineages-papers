import LogicLineages.PersistentMarking.MarkedConstructorSelectProof
import LogicLineages.PersistentMarking.MarkedConstructorFAbsExactProof

namespace LogicLineages.PersistentMarking.MarkedConstructorFieldsProof
open MarkedConstructorTargets

theorem fields : Fields := by
  intro S E heads M p Δ t
  refine ⟨rfl, rfl, ?_⟩
  simp only [MarkedConstructorValue.build, MarkedConstructorTests.weakTest,
    Bool.or_eq_true, MarkedConstructorSelectProof.select, MarkedConstructorFAbsExactProof.fabs]
  exact or_assoc.trans or_assoc

theorem exact_Fields : Fields := fields
#print axioms exact_Fields
end LogicLineages.PersistentMarking.MarkedConstructorFieldsProof
