module
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundBoxTargets
public import Mathlib.Data.List.GetD
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox

private theorem compOr {α : Type*} [Primcodable α] {f g : α → Bool}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x || g x) :=
  (hf.cond (Computable.const true) hg).of_eq (fun x => by cases f x <;> rfl)
private theorem negTrue (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide

theorem boxMembership : Targets.BoxMembership := by
  intro r m xs
  induction m generalizing xs with
  | zero => cases xs <;> simp [box]
  | succ m ih =>
    cases xs with
    | nil => simp [box]
    | cons x xs =>
      simp [box, ih, Nat.succ_le_iff, and_assoc, and_left_comm, and_comm]

theorem boxComputable : Targets.BoxComputable := by
  have hs : Primrec₂ (fun (r : Nat) (s : Nat × List (List Nat)) =>
      (List.range r).flatMap fun x => s.2.map (x :: ·)) :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  apply (Primrec.nat_rec (Primrec.const [[]]) hs).to_comp.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [box, ih]

private theorem prefixSpec {Q : Type*} (point : Q → List Nat → Bool) q tuples n :
    failingPrefix point q tuples n = true ↔
      ∃ i < n, point q (tuples.getD i []) = false := by
  induction n with
  | zero => simp [failingPrefix]
  | succ n ih =>
    simp only [failingPrefix, Bool.or_eq_true, negTrue, ih]
    constructor
    · rintro (⟨i, hi, hp⟩ | hp)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hp⟩
      · exact ⟨n, Nat.lt_succ_self n, hp⟩
    · rintro ⟨i, hi, hp⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact Or.inl ⟨i, hi, hp⟩
      · exact Or.inr hp

private theorem prefixComputable {Q : Type*} [Primcodable Q]
    (point : Q → List Nat → Bool) (hp : Computable₂ point) :
    Computable₂ (fun p : Q × List (List Nat) => failingPrefix point p.1 p.2) := by
  have hstep : Computable₂ (fun (a : (Q × List (List Nat)) × Nat) (s : Nat × Bool) =>
      s.2 || !(point a.1.1 (a.1.2.getD s.1 []))) :=
    compOr (Computable.snd.comp Computable.snd)
      (Primrec.not.to_comp.comp (hp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        ((Primrec.list_getD []).to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Computable.fst.comp Computable.snd))))
  have hc := Computable.nat_rec Computable.snd (Computable.const false) hstep
  apply hc.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [failingPrefix, ih]

theorem radiusComputable : Targets.RadiusComputable := by
  intro Q _ arity point ha hp
  have hb : Computable (fun p : Q × Nat => box p.2 (arity p.1)) :=
    boxComputable.comp Computable.snd (ha.comp Computable.fst)
  exact (prefixComputable point hp).comp (Computable.fst.pair hb)
    (Computable.list_length.comp hb)

theorem radiusCorrect : Targets.RadiusCorrect := by
  intro Q arity point q r
  rw [radiusBad, prefixSpec]
  constructor
  · rintro ⟨i, hi, hp⟩
    have hm : (box r (arity q)).getD i [] ∈ box r (arity q) := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    obtain ⟨hlen, hcoords⟩ := (boxMembership r (arity q) _).mp hm
    exact ⟨_, hlen, hcoords, hp⟩
  · rintro ⟨xs, hlen, hcoords, hp⟩
    have hm := (boxMembership r (arity q) xs).mpr ⟨hlen, hcoords⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hm
    refine ⟨i, hi, ?_⟩
    simpa only [List.getD_eq_getElem _ _ hi, heq] using hp

private theorem tupleBound (xs : List Nat) : ∃ r, ∀ x ∈ xs, x+1 ≤ r := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨max (x+1) r, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_max_left _ _
    · exact le_trans (hr y hy) (le_max_right _ _)

theorem exhaustive : Targets.Exhaustive := by
  intro Q arity point q
  constructor
  · intro hall xs hlen
    obtain ⟨r, hr⟩ := tupleBound xs
    cases hp : point q xs with
    | true => rfl
    | false =>
      have hb := (radiusCorrect arity point q r).mpr ⟨xs, hlen, hr, hp⟩
      simp [hall r] at hb
  · intro hall r
    cases hb : radiusBad arity point q r with
    | false => rfl
    | true =>
      obtain ⟨xs, hlen, _, hp⟩ := (radiusCorrect arity point q r).mp hb
      simp [hall xs hlen] at hp
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox
