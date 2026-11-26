import LogicLineages.PersistentMarking.MarkedConstructorSelectProof
import LogicLineages.PersistentMarking.MarkedConstructorFAbsExactProof

namespace LogicLineages.PersistentMarking.MarkedConstructorFieldsProof
open MarkedConstructorTargets

theorem fields : Fields := by
  intro S E heads M p Δ t
  refine ⟨rfl, rfl, ?_⟩
  let w := MarkedFamilyCoherence.weakenParameter E p Δ
  have hs := MarkedConstructorSelectProof.select E heads M w t
  have hf := MarkedConstructorFAbsExactProof.fabs E heads M w t
  change MarkedConstructorTests.weakTest S E heads M w t = true ↔ _
  simp only [MarkedConstructorTests.weakTest, Bool.or_eq_true, hs, hf, or_assoc]
  rfl

theorem exact_Fields : Fields := fields
#print axioms exact_Fields
end LogicLineages.PersistentMarking.MarkedConstructorFieldsProof
