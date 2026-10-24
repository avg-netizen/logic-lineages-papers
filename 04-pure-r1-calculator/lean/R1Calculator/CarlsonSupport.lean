import R1Calculator.SemanticBasics
import R1Calculator.FiniteDiagrams
import R1Calculator.ArithmeticBounds
import R1Calculator.EndpointClosure
import R1Calculator.NotationCoverage

/-!
# Induced tail copies over a fixed lower prefix

This is the finite-map content of Carlson's identity-extension lemma
(*Ordinal Arithmetic and Sigma-one Elementarity*, Lemma 2.9). It is proved
for the actual recursively constructed standalone pure R1. Both positive
and negative relation atoms are preserved; no endpoint formula is assumed.
-/

noncomputable section

namespace R1Calculator.PureR1

/-- The arithmetic candidate on ordinals, using actual normal notations.
Only the left point needs a notation witness. This is NOT a semantic R1
definition or an assumed correctness premise. Its local fixed-point
characterization below normal-notation bounds is proved in `Correctness.lean`. -/
def ArithmeticR1 (a b : Ordinal.{0}) : Prop :=
  ∃ c : NONote, c.repr = a ∧ a ≤ b ∧ b ≤ (endpointNF c).repr

theorem note_repr_injective : Function.Injective NONote.repr := by
  intro a b h
  apply le_antisymm
  · change a.repr ≤ b.repr
    exact h.le
  · change b.repr ≤ a.repr
    exact h.symm.le

/-- At every represented left endpoint the candidate has its exact arithmetic
interval meaning, even when the right point is not supplied as a notation. -/
theorem arithmeticR1_note_iff (a : NONote) (b : Ordinal.{0}) :
    ArithmeticR1 a.repr b ↔ a.repr ≤ b ∧ b ≤ (endpointNF a).repr := by
  constructor
  · rintro ⟨c, hc, hab, hbe⟩
    have he : c = a := note_repr_injective hc
    subst c
    exact ⟨hab, hbe⟩
  · intro h
    exact ⟨a, rfl, h⟩

theorem arithmeticR1_le {a b : Ordinal.{0}} (h : ArithmeticR1 a b) : a ≤ b := by
  obtain ⟨_, _, h, _⟩ := h
  exact h

theorem arithmeticR1_note_refl (a : NONote) : ArithmeticR1 a.repr a.repr :=
  (arithmeticR1_note_iff a a.repr).mpr ⟨le_rfl, repr_le_endpoint a.2⟩

/-- Every actual ordinal in a represented cut has the candidate diagonal atom.
This uses the proved notation-coverage theorem, not notation-only quantifiers. -/
theorem arithmeticR1_refl_below (b : NONote) {a : Ordinal.{0}} (ha : a ≤ b.repr) :
    ArithmeticR1 a a := by
  obtain ⟨c, hc, he⟩ := exists_nf_repr_of_le b.2 ha
  exact he ▸ arithmeticR1_note_refl ⟨c, hc⟩

theorem arithmeticR1_between {a b c : Ordinal.{0}} (hab : ArithmeticR1 a b)
    (hac : a ≤ c) (hcb : c ≤ b) : ArithmeticR1 a c := by
  obtain ⟨d, hd, _, hb⟩ := hab
  exact ⟨d, hd, hac, hcb.trans hb⟩

/-- The candidate is actually transitive: its endpoint-nesting premise has
been proved structurally from the arithmetic recurrence. -/
theorem arithmeticR1_trans {a b c : Ordinal.{0}} (hab : ArithmeticR1 a b)
    (hbc : ArithmeticR1 b c) : ArithmeticR1 a c := by
  obtain ⟨d, hd, hab, hbd⟩ := hab
  obtain ⟨e, he, hbc, hce⟩ := hbc
  have hde : d.repr ≤ e.repr := by simpa only [hd, he] using hab
  have hed : e.repr ≤ (endpointNF d).repr := by simpa only [he] using hbd
  have hend : (endpointNF e).repr ≤ (endpointNF d).repr :=
    endpoint_nested d.2 e.2 hde hed
  exact ⟨d, hd, hab.trans hbc, hce.trans hend⟩

theorem arithmeticR1_antisymm {a b : Ordinal.{0}} (hab : ArithmeticR1 a b)
    (hba : ArithmeticR1 b a) : a = b :=
  le_antisymm (arithmeticR1_le hab) (arithmeticR1_le hba)

theorem arithmeticR1_cross_cut {a b x y : Ordinal.{0}} (hab : ArithmeticR1 a b)
    (hx : x ≤ a) (hay : a ≤ y) (hyb : y ≤ b) :
    ArithmeticR1 x y ↔ ArithmeticR1 x a := by
  constructor
  · intro hxy
    exact arithmeticR1_between hxy hx hay
  · intro hxa
    exact arithmeticR1_trans hxa (arithmeticR1_between hab hay hyb)

theorem intervalCheck_iff_arithmeticR1 (a b : NONote) :
    intervalCheck a b = true ↔ ArithmeticR1 a.repr b.repr :=
  (intervalCheck_correct a b).trans (arithmeticR1_note_iff a b.repr).symm

/-- Positive-tail translation preserves the entire arithmetic relation, not
merely its endpoint value. This is a supplier for translated finite copies. -/
theorem arithmeticR1_add_right (a b c : NONote) (hb : b.1 ≠ 0) :
    ArithmeticR1 (a + b).repr (a + c).repr ↔ ArithmeticR1 b.repr c.repr := by
  have he : (endpointNF (a + b)).repr = a.repr + (endpointNF b).repr := by
    exact endpoint_add_right_repr a.2 b.2 hb
  rw [arithmeticR1_note_iff, arithmeticR1_note_iff, he,
    NONote.repr_add, NONote.repr_add]
  simp only [add_le_add_iff_left]

/-- Split off the final principal summand. The prefix is an ACTUAL ordinal,
so it is available as a fixed parameter in an endpoint obstruction. -/
theorem lastPrincipal_prefix : ∀ {a : ONote}, a.NF → a ≠ 0 →
    ∃ ξ : Ordinal.{0}, ξ < a.repr ∧
      a.repr = ξ + Ordinal.omega0 ^ (lastExponent a).repr
  | .zero, _, ha => (ha rfl).elim
  | .oadd e n t, ha, _ => by
      cases t with
      | zero =>
          let ρ : Ordinal.{0} := Ordinal.omega0 ^ e.repr
          let j : Nat := (n : Nat) - 1
          have heq : (ONote.oadd e n ONote.zero).repr = ρ * (j : Ordinal) + ρ := by
            have hn : (n : Nat) = j + 1 :=
              (Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)).symm
            change ρ * (n : Nat) + 0 = _
            rw [add_zero]
            calc
              ρ * (n : Nat) = ρ * ((j + 1 : Nat) : Ordinal) :=
                congrArg (fun q : Nat => ρ * (q : Ordinal)) hn
              _ = ρ * (j : Ordinal) + ρ := by
                simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
          refine ⟨ρ * (j : Ordinal), ?_, heq⟩
          have hp : 0 < ρ := Ordinal.opow_pos _ Ordinal.omega0_pos
          have hlt : ρ * (j : Ordinal) < ρ * (j : Ordinal) + ρ := by
            simpa only [add_zero] using (add_lt_add_iff_left (ρ * (j : Ordinal))).mpr hp
          exact hlt.trans_eq heq.symm
      | oadd d m s =>
          obtain ⟨ξ, hξ, heq⟩ := lastPrincipal_prefix (a := .oadd d m s)
            ha.snd (by intro h; cases h)
          refine ⟨Ordinal.omega0 ^ e.repr * (n : Nat) + ξ, ?_, ?_⟩
          · change Ordinal.omega0 ^ e.repr * (n : Nat) + ξ <
              Ordinal.omega0 ^ e.repr * (n : Nat) + (ONote.oadd d m s).repr
            exact (add_lt_add_iff_left _).mpr hξ
          · change Ordinal.omega0 ^ e.repr * (n : Nat) + (ONote.oadd d m s).repr = _
            rw [heq]
            exact (add_assoc _ _ _).symm

/-- Extend a proposed tail map by the identity at and below a cut. -/
def extendBelow (a : Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0})
    (x : Ordinal.{0}) : Ordinal.{0} :=
  if x ≤ a then x else g x

@[simp] theorem extendBelow_of_le {a x : Ordinal.{0}} (g : Ordinal.{0} → Ordinal.{0})
    (hx : x ≤ a) : extendBelow a g x = x := by simp [extendBelow, hx]

@[simp] theorem extendBelow_of_lt {a x : Ordinal.{0}} (g : Ordinal.{0} → Ordinal.{0})
    (hx : a < x) : extendBelow a g x = g x := by simp [extendBelow, not_le.mpr hx]

theorem R1_tail_to_prefix_false {a x y : Ordinal.{0}} (hx : x ≤ a) (hy : a < y) :
    ¬ R1 y x := by
  intro h
  exact (not_lt_of_ge (le_trans (R1_le h) hx)) hy

/-- Every target in the same R1 tail has exactly the same lower-prefix atoms. -/
theorem R1_cross_cut_congr {a b x y z : Ordinal.{0}} (hab : R1 a b)
    (hx : x ≤ a) (hy : a ≤ y) (hyb : y ≤ b) (hz : a ≤ z) (hzb : z ≤ b) :
    R1 x y ↔ R1 x z :=
  (R1_cross_cut hab hx hy hyb).trans (R1_cross_cut hab hx hz hzb).symm

/-- Extending an induced tail map by identity preserves the full finite diagram.
The source and image tail stay in `(a,b]`; the whole finite set stays below `b`.
This is a semantic R1 theorem, not a positive-covering substitute. -/
theorem preservesPattern_extendBelow {a b : Ordinal.{0}} (hab : R1 a b)
    (F : Finset Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0})
    (hF : ∀ x ∈ F, x ≤ b)
    (himage : ∀ x ∈ F, a < x → a < g x ∧ g x ≤ b)
    (htail : PreservesPattern R1 (F.filter (fun x => a < x)) g) :
    PreservesPattern R1 F (extendBelow a g) := by
  classical
  have tailmem {x : Ordinal.{0}} (hx : x ∈ F) (hax : a < x) :
      x ∈ F.filter (fun x => a < x) := Finset.mem_filter.mpr ⟨hx, hax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    by_cases hxa : x ≤ a
    · by_cases hya : y ≤ a
      · simp only [extendBelow_of_le g hxa, extendBelow_of_le g hya]
      · have hay : a < y := lt_of_not_ge hya
        have hagy := (himage y hy hay).1
        simp only [extendBelow_of_le g hxa, extendBelow_of_lt g hay]
        exact iff_of_false (ne_of_lt (lt_of_le_of_lt hxa hagy))
          (ne_of_lt (lt_of_le_of_lt hxa hay))
    · have hax : a < x := lt_of_not_ge hxa
      by_cases hya : y ≤ a
      · have hagx := (himage x hx hax).1
        simp only [extendBelow_of_lt g hax, extendBelow_of_le g hya]
        exact iff_of_false (ne_of_gt (lt_of_le_of_lt hya hagx))
          (ne_of_gt (lt_of_le_of_lt hya hax))
      · have hay : a < y := lt_of_not_ge hya
        simp only [extendBelow_of_lt g hax, extendBelow_of_lt g hay]
        exact htail.1 x (tailmem hx hax) y (tailmem hy hay)
  · intro x hx y hy
    by_cases hxa : x ≤ a
    · by_cases hya : y ≤ a
      · simp only [extendBelow_of_le g hxa, extendBelow_of_le g hya]
      · have hay : a < y := lt_of_not_ge hya
        have hagy := (himage y hy hay).1
        simp only [extendBelow_of_le g hxa, extendBelow_of_lt g hay]
        exact iff_of_true (lt_of_le_of_lt hxa hagy) (lt_of_le_of_lt hxa hay)
    · have hax : a < x := lt_of_not_ge hxa
      by_cases hya : y ≤ a
      · have hagx := (himage x hx hax).1
        simp only [extendBelow_of_lt g hax, extendBelow_of_le g hya]
        exact iff_of_false (not_lt_of_ge (le_of_lt (lt_of_le_of_lt hya hagx)))
          (not_lt_of_ge (le_of_lt (lt_of_le_of_lt hya hax)))
      · have hay : a < y := lt_of_not_ge hya
        simp only [extendBelow_of_lt g hax, extendBelow_of_lt g hay]
        exact htail.2.1 x (tailmem hx hax) y (tailmem hy hay)
  · intro x hx y hy
    by_cases hxa : x ≤ a
    · by_cases hya : y ≤ a
      · simp only [extendBelow_of_le g hxa, extendBelow_of_le g hya]
      · have hay : a < y := lt_of_not_ge hya
        have hg := himage y hy hay
        simp only [extendBelow_of_le g hxa, extendBelow_of_lt g hay]
        exact R1_cross_cut_congr hab hxa (le_of_lt hg.1) hg.2 (le_of_lt hay) (hF y hy)
    · have hax : a < x := lt_of_not_ge hxa
      by_cases hya : y ≤ a
      · have hg := himage x hx hax
        simp only [extendBelow_of_lt g hax, extendBelow_of_le g hya]
        exact iff_of_false (R1_tail_to_prefix_false hya hg.1)
          (R1_tail_to_prefix_false hya hax)
      · have hay : a < y := lt_of_not_ge hya
        simp only [extendBelow_of_lt g hax, extendBelow_of_lt g hay]
        exact htail.2.2 x (tailmem hx hax) y (tailmem hy hay)

/-- The extension also fixes every designated lower-prefix label pointwise. -/
theorem extendBelow_fixes_prefix (a : Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0})
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x ≤ a) :
    ∀ x ∈ X, extendBelow a g x = x := fun x hx => extendBelow_of_le g (hX x hx)

#print axioms R1_cross_cut_congr
#print axioms arithmeticR1_note_iff
#print axioms arithmeticR1_add_right
#print axioms arithmeticR1_trans
#print axioms arithmeticR1_refl_below
#print axioms lastPrincipal_prefix
#print axioms preservesPattern_extendBelow
#print axioms extendBelow_fixes_prefix

end R1Calculator.PureR1
