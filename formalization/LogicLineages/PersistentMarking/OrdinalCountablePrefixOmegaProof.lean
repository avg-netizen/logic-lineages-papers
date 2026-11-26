module

public import LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaTargets

public section

namespace LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaProof
open OrdinalCountablePrefixOmegaTargets
open scoped Ordinal

theorem exact_CountablePrefixIffBelowOmegaOne : CountablePrefixIffBelowOmegaOne := by
  intro o
  change (Set.Iio o).Countable ↔ o < ω₁
  rw [Cardinal.countable_iff_lt_aleph_one, Cardinal.mk_Iio_ordinal, Cardinal.lt_omega_iff_card_lt]
  simp only [Cardinal.lt_aleph_one_iff, Cardinal.lift_le_aleph0]

#print axioms exact_CountablePrefixIffBelowOmegaOne

end LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaProof
