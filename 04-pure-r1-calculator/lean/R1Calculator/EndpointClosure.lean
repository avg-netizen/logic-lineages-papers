import R1Calculator.ArithmeticLaws

/-! Arithmetic nesting of the computed endpoint intervals. These statements
are proved without a hypothesis identifying the intervals with elementarity. -/

namespace R1Calculator

open Ordinal ONote Order

def EndpointClosed (c : Ordinal) : Prop :=
  ∀ a : ONote, NF a → a.repr ≤ c → (endpoint a).repr ≤ c

private theorem add_sub_note {a b : ONote} (ha : NF a) (hb : NF b)
    (hab : a.repr ≤ b.repr) : a + (b - a) = b := by
  haveI : NF a := ha
  haveI : NF b := hb
  apply ONote.repr_inj.mp
  rw [ONote.repr_add, ONote.repr_sub]
  exact Ordinal.add_sub_cancel_of_le hab

private theorem sub_note_ne_zero {a b : ONote} (ha : NF a) (hb : NF b)
    (hab : a.repr < b.repr) : b - a ≠ 0 := by
  intro hz
  haveI : NF a := ha
  haveI : NF b := hb
  have heq := congrArg ONote.repr (add_sub_note ha hb hab.le)
  simp only [hz, ONote.repr_add, ONote.repr_zero, add_zero] at heq
  exact hab.ne heq

theorem endpointClosed_add {a b : ONote} (ha : NF a) (_hb : NF b)
    (hca : EndpointClosed a.repr) (hcb : EndpointClosed b.repr) :
    EndpointClosed (a.repr + b.repr) := by
  intro c hc hle
  by_cases hca' : c.repr ≤ a.repr
  · exact (hca c hc hca').trans le_self_add
  have hac : a.repr < c.repr := lt_of_not_ge hca'
  haveI : NF a := ha
  haveI : NF c := hc
  have hsum := add_sub_note ha hc hac.le
  have hrem : (c - a).repr ≤ b.repr := by
    have heq := congrArg ONote.repr hsum
    rw [ONote.repr_add] at heq
    rw [← heq] at hle
    exact (add_le_add_iff_left a.repr).mp hle
  rw [← hsum, endpoint_add_right_repr ha (ONote.sub_nf c a)
    (sub_note_ne_zero ha hc hac)]
  exact add_le_add_right (hcb (c - a) (ONote.sub_nf c a) hrem) _

private theorem endpoint_monomial_repr (e : ONote) (n : ℕ+) (he : NF e) :
    (endpoint (.oadd e n 0)).repr = (ONote.oadd e n 0).repr + (principalSum e).repr := by
  haveI : NF e := he
  haveI : NF (principalSum e) := principalSum_nf he
  change (ONote.oadd e n 0 + principalSum e).repr = _
  exact ONote.repr_add _ _

/-- A principal coefficient block followed by a closed tail is closed if
the tail contains that block's correction. -/
theorem endpointClosed_monomial_plus {e r : ONote} (n : ℕ+)
    (he : NF e) (_hr : NF r) (hcr : EndpointClosed r.repr)
    (hcorrection : (principalSum e).repr ≤ r.repr) :
    EndpointClosed ((ONote.oadd e n 0).repr + r.repr) := by
  intro a ha hle
  haveI : NF e := he
  haveI : NF a := ha
  let m : ONote := .oadd e n 0
  have hm : NF m := he.oadd n NFBelow.zero
  by_cases hlow : a.repr < m.repr
  · have hsmall := endpoint_lt_monomial_bound (d := e.repr) (n := (n : ℕ)) ha
        (show a.repr < ω ^ e.repr * (n : ℕ) from by simpa [m, ONote.repr] using hlow)
    have hsmall' : (endpoint a).repr < m.repr := by
      simpa [m, ONote.repr] using hsmall
    exact hsmall'.le.trans le_self_add
  have hma : m.repr ≤ a.repr := le_of_not_gt hlow
  by_cases heq : a.repr = m.repr
  · have hsyntax : a = m := ONote.repr_inj.mp heq
    rw [hsyntax, endpoint_monomial_repr e n he]
    exact add_le_add_right hcorrection _
  have hstrict : m.repr < a.repr := lt_of_le_of_ne hma (Ne.symm heq)
  haveI : NF m := hm
  have hsum := add_sub_note hm ha hma
  have hrem : (a - m).repr ≤ r.repr := by
    have heq' := congrArg ONote.repr hsum
    rw [ONote.repr_add] at heq'
    rw [← heq'] at hle
    exact (add_le_add_iff_left m.repr).mp hle
  rw [← hsum, endpoint_add_right_repr hm (ONote.sub_nf a m)
    (sub_note_ne_zero hm ha hstrict)]
  exact add_le_add_right (hcr (a - m) (ONote.sub_nf a m) hrem) _

private theorem finite_block_tail (e : ONote) (n : ℕ+) (he : NF e) :
    (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) =
      ω ^ e.repr * (n : ℕ) + (principalSum e).repr := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt n.pos)
  have habs : (principalSum e).repr + ω ^ e.repr = ω ^ e.repr :=
    Ordinal.add_of_omega0_opow_le (principalSum_repr_lt_omega_opow he) le_rfl
  simpa only [hk, Nat.cast_succ] using Ordinal.add_mul_add_one (k : Ordinal) habs

/-- Every principal-sum output is an actual closed arithmetic horizon. -/
theorem principalSum_endpointClosed : ∀ {e : ONote}, NF e →
    EndpointClosed (principalSum e).repr
  | .zero, _ => by
      intro a ha hle
      haveI : NF a := ha
      have heq : a = 0 := ONote.repr_inj.mp (le_antisymm hle bot_le)
      subst a
      exact le_rfl
  | .oadd d n t, h => by
      haveI : NF d := h.fst
      haveI : NF t := h.snd
      haveI : NF (principalSum d) := principalSum_nf h.fst
      haveI : NF (principalSum t) := principalSum_nf h.snd
      let r : ONote := principalSum d + principalSum t
      have hr : NF r := ONote.add_nf _ _
      have hcr : EndpointClosed r.repr := by
        rw [show r.repr = (principalSum d).repr + (principalSum t).repr from ONote.repr_add _ _]
        exact endpointClosed_add (principalSum_nf h.fst) (principalSum_nf h.snd)
          (principalSum_endpointClosed h.fst) (principalSum_endpointClosed h.snd)
      have hcorrection : (principalSum d).repr ≤ r.repr := by
        change (principalSum d).repr ≤ (principalSum d + principalSum t).repr
        rw [ONote.repr_add]
        exact le_self_add
      have hP : (principalSum (.oadd d n t)).repr = (ONote.oadd d n 0).repr + r.repr := by
        rw [principalSum_step_repr n h, finite_block_tail d n h.fst,
          show r.repr = (principalSum d).repr + (principalSum t).repr from ONote.repr_add _ _]
        simp only [ONote.repr, add_zero, add_assoc]
      rw [hP]
      exact endpointClosed_monomial_plus n h.fst hr hcr hcorrection

/-- Computed endpoint intervals nest: this is the arithmetic forest law,
proved independently of Carlson's semantic characterization. -/
theorem endpoint_nested {a b : ONote} (ha : NF a) (hb : NF b)
    (hab : a.repr ≤ b.repr) (hba : b.repr ≤ (endpoint a).repr) :
    (endpoint b).repr ≤ (endpoint a).repr := by
  by_cases heq : a.repr = b.repr
  · haveI : NF a := ha
    haveI : NF b := hb
    exact (congrArg (fun c => (endpoint c).repr) (ONote.repr_inj.mp heq)).symm.le
  have hlt : a.repr < b.repr := lt_of_le_of_ne hab heq
  haveI : NF a := ha
  haveI : NF b := hb
  haveI : NF (principalSum (lastExponent a)) := principalSum_nf (lastExponent_nf ha)
  have hsum := add_sub_note ha hb hab
  have hrem : (b - a).repr ≤ (principalSum (lastExponent a)).repr := by
    have heq' := congrArg ONote.repr hsum
    rw [ONote.repr_add] at heq'
    rw [← heq', endpoint, ONote.repr_add] at hba
    exact (add_le_add_iff_left a.repr).mp hba
  have hend := principalSum_endpointClosed (lastExponent_nf ha)
    (b - a) (ONote.sub_nf b a) hrem
  rw [← hsum, endpoint_add_right_repr ha (ONote.sub_nf b a)
    (sub_note_ne_zero ha hb hlt)]
  rw [show (endpoint a).repr = a.repr + (principalSum (lastExponent a)).repr
    from ONote.repr_add a (principalSum (lastExponent a))]
  exact add_le_add_right hend _

#print axioms principalSum_endpointClosed
#print axioms endpoint_nested

end R1Calculator
