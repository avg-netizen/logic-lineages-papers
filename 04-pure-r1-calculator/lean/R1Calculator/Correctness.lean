import R1Calculator.Carlson

/-!
# Semantic correctness of the standalone pure-R1 endpoint calculator

The arithmetic candidate is proved to satisfy the actual Sigma-one recursive
equation below every normal-notation bound. Recursive uniqueness identifies it
with the independently constructed semantic relation. The resulting endpoint
statement quantifies over ALL actual right ordinals, not only notation inputs.
No semantic characterization, copy constructor or obstruction is a hypothesis
of the public correctness theorems below.
-/

noncomputable section
namespace R1Calculator.PureR1

open Ordinal Order

/-- An explicit next normal notation, used only to choose a larger proof bound. -/
def successorNote (a : NONote) : NONote :=
  ⟨a.val + ONote.ofNat 1, ONote.add_nf a.val (ONote.ofNat 1)⟩

theorem successorNote_repr (a : NONote) : (successorNote a).repr = a.repr + 1 := by
  change (a.val + ONote.ofNat 1).repr = a.val.repr + 1
  simp only [ONote.repr_add, ONote.repr_ofNat, Nat.cast_one]

/-- The fixed-point equation is a theorem, assembled from the proved finite
copy construction and the proved finite obstruction. -/
theorem arithmeticR1_fixedpoint_below (bound : NONote) (α β : Ordinal.{0})
    (hβ : β < bound.repr) :
    ArithmeticR1 α β ↔ α ≤ β ∧ Sigma1Elementary ArithmeticR1 α β := by
  constructor
  · rintro ⟨a, rfl, hab, hb⟩
    exact ⟨hab, (sigma1Elementary_iff_finiteReflection ArithmeticR1 a.repr β hab).mpr
      (OrderedForest.arithmetic_finiteReflection_of_interval a β hab hb)⟩
  · rintro ⟨hab, hs⟩
    obtain ⟨a, ha⟩ := exists_nonote_repr_of_lt bound (hab.trans_lt hβ)
    have href := (sigma1Elementary_iff_finiteReflection ArithmeticR1 α β hab).mp hs
    have hupper : β ≤ (endpointNF a).repr := by
      by_contra hn
      apply OrderedForest.arithmetic_not_finiteReflection_above a β (lt_of_not_ge hn)
      simpa only [ha] using href
    exact ⟨a, ha, hab, hupper⟩

theorem arithmeticR1_iff_R1_below (bound : NONote) (α β : Ordinal.{0})
    (hβ : β < bound.repr) : ArithmeticR1 α β ↔ R1 α β :=
  R1_unique_below bound.repr ArithmeticR1
    (arithmeticR1_fixedpoint_below bound) α β hβ

/-- Carlson's interval characterization on normal notation inputs, derived
from the actual recursive semantics rather than cited as an assumption. -/
theorem R1_note_iff (a b : NONote) :
    R1 a.repr b.repr ↔ a.repr ≤ b.repr ∧ b.repr ≤ (endpointNF a).repr := by
  have hb : b.repr < (successorNote b).repr := by
    rw [successorNote_repr]
    exact lt_add_of_pos_right _ zero_lt_one
  exact (arithmeticR1_iff_R1_below (successorNote b) a.repr b.repr hb).symm.trans
    (arithmeticR1_note_iff a b.repr)

/-- Full endpoint row: the right point may be ANY actual ordinal.
The obstruction at H(a)+1 rules out all larger ordinals by downwardness. -/
theorem endpoint_semantic (a : NONote) (β : Ordinal.{0}) :
    R1 a.repr β ↔ a.repr ≤ β ∧ β ≤ (endpointNF a).repr := by
  constructor
  · intro h
    refine ⟨R1_le h, ?_⟩
    by_contra hn
    have hlarge : (endpointNF a).repr < β := lt_of_not_ge hn
    let b := successorNote (endpointNF a)
    have hb : b.repr = (endpointNF a).repr + 1 := successorNote_repr _
    have hab : a.repr ≤ b.repr :=
      (repr_le_endpoint a.property).trans (by rw [hb]; exact le_self_add)
    have hbβ : b.repr ≤ β := by
      rw [hb]
      exact add_one_le_of_lt hlarge
    have hbad := ((R1_note_iff a b).mp (R1_between h hab hbβ)).2
    rw [hb] at hbad
    exact (not_le_of_gt (lt_add_of_pos_right (endpointNF a).repr zero_lt_one)) hbad
  · rintro ⟨hab, hb⟩
    obtain ⟨b, heq⟩ := exists_nonote_repr_of_le (endpointNF a) hb
    have h := (R1_note_iff a b).mpr
      ⟨by simpa only [heq] using hab, by simpa only [heq] using hb⟩
    simpa only [heq] using h

theorem intervalCheck_iff_R1 (a b : NONote) :
    intervalCheck a b = true ↔ R1 a.repr b.repr :=
  (intervalCheck_correct a b).trans (R1_note_iff a b).symm

theorem intervalCheck_iff_sigma1 (a b : NONote) :
    intervalCheck a b = true ↔ a.repr ≤ b.repr ∧ Sigma1Elementary R1 a.repr b.repr :=
  (intervalCheck_iff_R1 a b).trans (R1_iff_global a.repr b.repr)

theorem endpoint_isGreatest (a : NONote) :
    IsGreatest {β : Ordinal.{0} | R1 a.repr β} (endpointNF a).repr := by
  constructor
  · exact (endpoint_semantic a _).mpr ⟨repr_le_endpoint a.property, le_rfl⟩
  · intro β hβ
    exact ((endpoint_semantic a β).mp hβ).2

#print axioms arithmeticR1_fixedpoint_below
#print axioms endpoint_semantic
#print axioms intervalCheck_iff_R1
#print axioms intervalCheck_iff_sigma1
#print axioms endpoint_isGreatest

end R1Calculator.PureR1
