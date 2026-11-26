module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowGuardedSemanticTargets
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.EntryResiduesProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow
open OrdinalComparison FieldComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private def rowFrom (m k nmu : Nat) (c u v : Int) (js : List Nat) : NormalForm.Formula :=
  js.foldr (fun j tail => if keepResidue m k nmu j c u v then
    .disjunction (residueAtom m j) tail else tail) .falsity

private theorem zeroGapLong (lam mu : NONote) (hp : ProperField (.entry 0 lam mu)) :
    shortGapLength lam mu = 0 ↔ LongField (.entry 0 lam mu) := by
  constructor
  · intro hz
    refine ⟨hp.1,hp.2.1,hp.2.2,?_⟩
    rintro ⟨k,hk,hend⟩
    exact (Nat.ne_of_gt hk) (((shortGapRecognition lam mu hp k hk).2.2.mpr hend).symm.trans hz)
  · intro hl
    rcases Nat.eq_zero_or_pos (shortGapLength lam mu) with hz | hk
    · exact hz
    · exact (hl.2.2.2 ⟨_,hk,(shortGapRecognition lam mu hp _ hk).2.2.mp rfl⟩).elim

private theorem residueAtomEval (m j : Nat) (hm : 0 < m) (ν : Nat → Nat) :
    (residueAtom m j).eval ν ↔ Nat.ModEq (2*m) j (ν 1) := by
  have hmod : 2*m-1+1 = 2*m := by omega
  have hsum : -(j : Int) + (ν 1 : Int) = (ν 1 : Int) - j := by omega
  simp only [residueAtom,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NormalForm.Summand.term,
    OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul,add_zero,hmod]
  rw [hsum]
  exact Int.modEq_iff_dvd.symm.trans Int.natCast_modEq_iff

private theorem rowFromEval (m k nmu : Nat) (c u v : Int) (ν : Nat → Nat) (js : List Nat) :
    (rowFrom m k nmu c u v js).eval ν ↔
      ∃ j ∈ js, keepResidue m k nmu j c u v = true ∧ (residueAtom m j).eval ν := by
  induction js with
  | nil => simp [rowFrom,NormalForm.Formula.eval]
  | cons j js ih =>
    by_cases h : keepResidue m k nmu j c u v = true
    · change ((if keepResidue m k nmu j c u v then
        .disjunction (residueAtom m j) (rowFrom m k nmu c u v js) else
          rowFrom m k nmu c u v js) : NormalForm.Formula).eval ν ↔ _
      rw [if_pos h]
      change ((residueAtom m j).eval ν ∨ (rowFrom m k nmu c u v js).eval ν) ↔ _
      rw [ih]
      constructor
      · rintro (hj | ⟨l,hl,hkeep,ha⟩)
        · exact ⟨j,List.mem_cons_self,h,hj⟩
        · exact ⟨l,List.mem_cons_of_mem _ hl,hkeep,ha⟩
      · rintro ⟨l,hl,hkeep,ha⟩
        rcases List.mem_cons.mp hl with he | ht
        · subst l
          exact Or.inl ha
        · exact Or.inr ⟨l,ht,hkeep,ha⟩
    · change ((if keepResidue m k nmu j c u v then
        .disjunction (residueAtom m j) (rowFrom m k nmu c u v js) else
          rowFrom m k nmu c u v js) : NormalForm.Formula).eval ν ↔ _
      rw [if_neg h,ih]
      constructor
      · rintro ⟨l,hl,hkeep,ha⟩
        exact ⟨l,List.mem_cons_of_mem _ hl,hkeep,ha⟩
      · rintro ⟨l,hl,hkeep,ha⟩
        rcases List.mem_cons.mp hl with he | ht
        · subst l
          exact (h hkeep).elim
        · exact ⟨l,ht,hkeep,ha⟩

private theorem keepResidueExact (m k nmu j : Nat) (c u v : Int) :
    keepResidue m k nmu j c u v = true ↔
      (m : Int) ∣ c + u * (j : Int) + v * residueCount k nmu j := by
  simp only [keepResidue,decide_eq_true_eq]
  rw [← Nat.dvd_iff_mod_eq_zero,← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]

private theorem rowAt (m k nmu x : Nat) (hm : 0 < m) (c u v : Int)
    (ν : Nat → Nat) (hν : ν 1 = x) :
    (row m k nmu c u v).eval ν ↔
      (m : Int) ∣ c + u * ((x%(2*m) : Nat) : Int) + v * residueCount k nmu (x%(2*m)) := by
  change (rowFrom m k nmu c u v (List.range (2*m))).eval ν ↔ _
  rw [rowFromEval]
  constructor
  · rintro ⟨j,hj,hkeep,ha⟩
    have hlt : j < 2*m := List.mem_range.mp hj
    have he := (residueAtomEval m j hm ν).mp ha
    rw [hν] at he
    have hsame : j = x%(2*m) := (Nat.mod_eq_of_lt hlt).symm.trans he
    subst j
    exact (keepResidueExact _ _ _ _ _ _ _).mp hkeep
  · intro h
    have hm' : 0 < 2*m := by omega
    refine ⟨x%(2*m),List.mem_range.mpr (Nat.mod_lt _ hm'),
      (keepResidueExact _ _ _ _ _ _ _).mpr h,?_⟩
    apply (residueAtomEval m _ hm ν).mpr
    rw [hν]
    exact Nat.mod_mod _ _

theorem actualNamedRowGuarded : ActualNamedRowGuarded := by
  intro f B hf m rank lam mu c u v ρ hm hp
  dsimp only
  intro ht
  let x := ρ rank
  let j := x%(2*m)
  let k := shortGapLength lam mu
  let nmu := actualOrdinalNorm mu.1.repr
  have hx : max (actualOrdinalNorm lam.1.repr) (max (nmu+3) (max m B)) ≤ x := by
    simpa only [tailCode,normal_norm_code] using ht
  obtain ⟨i,hi,_,hshort,hlong⟩ :=
    entryResidues f B hf m lam.1.repr mu.1.repr x hm
      (rawNotation_repr_lt_epsilonZero lam.1) hp.1 hp.2.1 hp.2.2 hx
  have hdom : ClosedOrdinaryValueDomain (.entry 0 lam mu) x :=
    ⟨hp,(le_max_left _ _).trans hx⟩
  have ha : LowerOperandActual f ρ (.count rank lam mu) i := ⟨hdom,hi⟩
  have hr := (preparedTiedProjection.1 f ρ (.count rank lam mu) i).mpr ha
  refine ⟨i,hi,hdom,ha,hr,?_⟩
  intro ν hν
  have hj : Int.ModEq (m : Int) (x : Int) (j : Int) := by
    apply Int.natCast_modEq_iff.mpr
    change x%m = (x%(2*m))%m
    exact (Nat.mod_mod_of_dvd x (Nat.dvd_mul_left m 2)).symm
  have hfloor : Int.ModEq (m : Int) (potential x : Int) ((j / 2 : Nat) : Int) := by
    apply Int.natCast_modEq_iff.mpr
    change (x/2)%m = (j/2)%m
    calc
      (x/2)%m = ((x/2)%m)%m := (Nat.mod_mod (x/2) m).symm
      _ = (j/2)%m := congrArg (fun n : Nat => n%m) (Nat.mod_mul_right_div_self x 2 m).symm
  have hiMod : Int.ModEq (m : Int) (i : Int) (residueCount k nmu j) := by
    by_cases hzero : k = 0
    · have hshape := (zeroGapLong lam mu hp).mp hzero
      have hc := (hlong hshape.2.2.2).1
      have hpmod := hfloor.sub_right (((nmu+1)/2 : Nat) : Int)
      simpa only [residueCount,if_pos hzero] using hc.trans hpmod
    · have hk : 0 < k := Nat.pos_of_ne_zero hzero
      have he := (shortGapRecognition lam mu hp k hk).2.2.mp rfl
      have hij := hshort k hk he
      rw [residueCount,if_neg hzero,hij] <;> exact Int.ModEq.refl _
  have hs := ((hj.mul_left u).add_left c).add (hiMod.mul_left v)
  exact (rowAt m k nmu x hm c u v ν hν).trans hs.dvd_iff.symm

end LogicLineages.PermittedControl.CountCongruenceNamedRow
