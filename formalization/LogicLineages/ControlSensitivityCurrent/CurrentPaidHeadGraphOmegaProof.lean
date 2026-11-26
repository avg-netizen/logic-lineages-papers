module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationTargets
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaOrderProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentArithmeticProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open FunctionalDetector.Proof

/-- At limits, insertion of a finite omega coefficient is also ordinary
right addition. The overlap at exponent one is explicitly allowed. -/
theorem sumOmegaTail (β : Ordinal) (he : β<epsilonZero) (hl : Order.IsSuccLimit β) (n : Nat) :
    ordinalNaturalSum β (Ordinal.omega0*(n : Ordinal))=shiftHead β n := by
  unfold ordinalNaturalSum shiftHead
  rw [Ordinal.CNF.eval_add,Ordinal.CNF.eval_coeff,Ordinal.CNF.eval_coeff]
  intro a ha b hb
  have hd : Ordinal.omega0^(1 : Ordinal) ∣ β := by
    simpa only [Ordinal.opow_one] using Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
  have hm := (actualMinExponentDivisibility β he 1).mpr hd
  rw [Ordinal.CNF.support_coeff] at ha
  obtain ⟨⟨a',c⟩,hc,hac⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  change a'=a at hac
  subst a'
  have hb' : b=1 := by
    by_cases hz : n=0
    · simp [hz] at hb
    have hne : (n : Ordinal)≠0 := by exact_mod_cast hz
    have hn : Ordinal.CNF.coeff Ordinal.omega0 (Ordinal.omega0*(n : Ordinal)) =
        Finsupp.single 1 (n : Ordinal) := by
      simpa only [Ordinal.opow_one,add_zero,Ordinal.CNF.coeff_zero_right] using
        Ordinal.CNF.coeff_opow_mul_add (e:=1) (x:=(n : Ordinal)) (y:=0)
          Ordinal.one_lt_omega0 hne (Ordinal.natCast_lt_omega0 n)
          (by simpa only [Ordinal.opow_one] using Ordinal.omega0_pos)
    rw [hn] at hb
    by_contra hbne
    exact (Finsupp.mem_support_iff.mp hb) (Finsupp.single_eq_of_ne hbne)
  rw [hb']
  exact hm (a,c) hc

private theorem shiftExponent (e : ONote) (he : ONote.NF e) :
    (rawNaturalSum 1 e).repr=e.repr+1 := by
  have h := naturalSumDenotation (⟨1,ONote.nf_one⟩ : NONote) (⟨e,he⟩ : NONote)
  change (rawNaturalSum 1 e).repr=ordinalNaturalSum (1 : ONote).repr e.repr at h
  rw [h,ONote.repr_one,sum_comm]
  simpa using actualNaturalSumFiniteRight e.repr 1

private def shiftNote : ONote → ONote
  | .zero => .zero
  | .oadd e c t => .oadd (rawNaturalSum 1 e) c (shiftNote t)

private theorem shiftBelow : ∀ (t : ONote) (b : Ordinal), ONote.NFBelow t b →
    ONote.NFBelow (shiftNote t) (b+1)
  | .zero,_,_ => ONote.NFBelow.zero
  | .oadd e c t,b,ht => by
    apply ONote.NFBelow.oadd (rawNaturalSum_normal 1 e ONote.nf_one ht.fst)
    · simpa only [shiftExponent e ht.fst] using shiftBelow t e.repr ht.snd
    · rw [shiftExponent e ht.fst,← Order.succ_eq_add_one,← Order.succ_eq_add_one]
      exact Order.succ_lt_succ ht.lt

private theorem sumSingleton (e : ONote) (c : ℕ+) (t : ONote)
    (he : ONote.NF e) (ht : ONote.NFBelow t e.repr) :
    rawNaturalSum (.oadd e c .zero) t=.oadd e c t := by
  cases t with
  | zero => simp only [rawNaturalSum]
  | oadd f d u =>
    have h : ONote.cmp e f=.gt := (@ONote.cmp_compares e f he ht.fst).eq_gt.mpr ht.lt
    simp only [rawNaturalSum,h]

private theorem monomialShift : ∀ (t : ONote), ONote.NF t → rawMonomialProduct 1 1 t=shiftNote t
  | .zero,_ => rfl
  | .oadd e c t,ht => by
    simp only [rawMonomialProduct,monomialShift t ht.snd,one_mul,shiftNote]
    apply sumSingleton
    · exact rawNaturalSum_normal 1 e ONote.nf_one ht.fst
    · rw [shiftExponent e ht.fst]
      exact shiftBelow t e.repr ht.snd'

private theorem shiftValue (t : NONote) :
    (shiftNote t.1).repr=ordinalNaturalProduct Ordinal.omega0 t.1.repr := by
  let w : NONote := ⟨.oadd 1 1 .zero,ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hw : w.1.repr=Ordinal.omega0 := by simp [w,ONote.repr]
  have hd := naturalProductDenotation w t
  change (rawNaturalProduct w.1 t.1).repr=_ at hd
  rw [hw] at hd
  have hsum : rawNaturalProduct w.1 t.1=shiftNote t.1 := by
    change rawNaturalSum (rawMonomialProduct 1 1 t.1) .zero=shiftNote t.1
    rw [monomialShift t.1 t.2]
    cases shiftNote t.1 <;> simp only [rawNaturalSum]
  rwa [hsum] at hd

private theorem shiftFinite (a : ONote) (ha : ONote.NF a) (m : ℕ+) :
    (shiftNote (rawNaturalSum a (.oadd .zero m .zero))).repr =
      (shiftNote a).repr+Ordinal.omega0*(m : Nat) := by
  induction a with
  | zero =>
    change (shiftNote (rawNaturalSum ONote.zero (.oadd .zero m .zero))).repr =
      (0 : Ordinal)+Ordinal.omega0*(m : Nat)
    rw [rawNaturalSum]
    change Ordinal.omega0^(rawNaturalSum 1 ONote.zero).repr*(m : Nat)+0 = _
    simp only [shiftExponent ONote.zero ONote.NF.zero,add_zero,zero_add]
    change Ordinal.omega0 ^ ((0 : Ordinal)+1) * (m : Nat) = Ordinal.omega0*(m : Nat)
    simp only [zero_add,Ordinal.opow_one]
  | oadd e c t ihe iht =>
    have hc := @ONote.cmp_compares e .zero ha.fst ONote.NF.zero
    cases h : ONote.cmp e .zero with
    | lt =>
      have hf : e.repr<0 := hc.eq_lt.mp h
      exact (not_lt_of_ge zero_le hf).elim
    | eq =>
      have he := ONote.eq_of_cmp_eq h
      subst e
      have ht : t=.zero := ONote.NFBelow_zero.mp ha.snd'
      subst t
      simp only [rawNaturalSum,h,shiftNote,ONote.repr,PNat.add_coe,Nat.cast_add,
        add_zero,mul_add]
      simp
    | gt =>
      simp only [rawNaturalSum,h,shiftNote,ONote.repr]
      rw [show (shiftNote (rawNaturalSum t (.oadd .zero m .zero))).repr = _ from iht ha.snd]
      exact (add_assoc _ _ _).symm

/-- Exact product with omega after an actual finite-right addition, at the
written exponent and coefficient convention, without ordinary left product
being substituted on arbitrary nonfinite input. -/
theorem productOmegaTail (k : Ordinal) (hk : k<epsilonZero) (n : Nat) :
    ordinalNaturalProduct Ordinal.omega0 (k+(n : Ordinal)) =
      shiftHead (ordinalNaturalProduct Ordinal.omega0 k) n := by
  cases n with
  | zero => simp only [Nat.cast_zero,add_zero,shiftHead,mul_zero]
  | succ d =>
    obtain ⟨a,ha⟩ := normalRepresentationComplete k hk
    let m : ℕ+ := ⟨d+1,Nat.succ_pos d⟩
    let x : NONote := NONote.ofNat (d+1)
    have hx : x.1=.oadd .zero m .zero := rfl
    have hsum := naturalSumDenotation a x
    change (naturalSum a x).1.repr=ordinalNaturalSum a.1.repr x.1.repr at hsum
    have hv : x.1.repr=((d+1 : Nat) : Ordinal) := by
      change (ONote.ofNat (d+1)).repr=((d+1 : Nat) : Ordinal)
      exact ONote.repr_ofNat _
    rw [ha,hv,actualNaturalSumFiniteRight] at hsum
    rw [← hsum,← shiftValue,← ha,← shiftValue]
    change (shiftNote (rawNaturalSum a.1 x.1)).repr = shiftHead (shiftNote a.1).repr (d+1)
    rw [hx]
    exact shiftFinite a.1 a.2 m

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
