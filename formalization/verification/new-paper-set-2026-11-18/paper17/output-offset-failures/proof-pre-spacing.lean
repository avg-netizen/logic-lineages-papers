module
public import LogicLineages.PermittedControl.OutputOffsetTargets
public import LogicLineages.PermittedControl.CocycleProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem properEntryRange : Targets.ProperEntryRange := by
  intro f B hf lambda mu t hl hll hm hml ht
  obtain ⟨i,hi,hN⟩ := entryExistenceOrbit f B hf lambda mu t hl hll hm hml ht
  have hip : 0<i := by
    by_contra hn
    have he : i=0 := by omega
    have hbad := hi.2.1
    rw [he,Function.iterate_zero_apply] at hbad
    have hs := limit_interval_separation mu lambda hm hll hml
    have ha : lambda≤countInitial lambda t := le_self_add
    exact (not_lt_of_ge (hs.trans ha)) hbad
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  refine ⟨j+1,f^[j] t,by omega,hi,hN,?_,?_⟩
  · rw [hN,Function.iterate_succ_apply']
  · rw [hN]
    exact iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) _ t

 theorem entryRangeExponentialSeparation : Targets.EntryRangeExponentialSeparation := by
  intro f B hf U V hU hV hUV
  obtain ⟨u,rfl⟩ := hU
  obtain ⟨v,rfl⟩ := hV
  have hs := (selected_threshold_admissible f B hf).1
  have huv : u<v := hs.lt_iff_lt.mp hUV
  have hg := (selected_laws f B hf).2.2.2.1 u
  have hp : f u+1≤2^(f u) := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=f u))
  exact (Nat.pow_le_pow_right (by omega) hp).trans
    (hg.trans (hs.monotone (by omega)))

 theorem signed_offset_abs (c : Nat) : (signedOffsetValue c).natAbs=c/2+c%2 := by
  have hr : c%2<2 := Nat.mod_lt _ (by omega)
  by_cases hz : c%2=0
  · simp [signedOffsetValue,hz]
  · have ho : c%2=1 := by omega
    simp [signedOffsetValue,hz,ho]

 theorem signedOffsetTailEffective : Targets.SignedOffsetTailEffective := by
  have ha : Primrec (fun p : Nat×Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : Nat×Nat => p.2) := Primrec.snd
  have had := Primrec.nat_div.comp ha (Primrec.const 2)
  have ham := Primrec.nat_mod.comp ha (Primrec.const 2)
  have hbd := Primrec.nat_div.comp hb (Primrec.const 2)
  have hbm := Primrec.nat_mod.comp hb (Primrec.const 2)
  refine ⟨Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp had ham) hbd) hbm) (Primrec.const 2),?_,?_⟩
  · intro a
    cases a with
    | ofNat n =>
      refine ⟨2*n,?_⟩
      simp [signedOffsetValue]
    | negSucc n =>
      refine ⟨2*n+1,?_⟩
      simp [signedOffsetValue,Int.negSucc_eq]
  · intro a b
    rw [signed_offset_abs,signed_offset_abs]
    unfold outputOffsetTailCode
    omega

 theorem offset_strict_order (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (U V : Nat) (a b : Int) (hU : ∃u,f u=U) (hV : ∃v,f v=V)
    (hUV : U<V) (hsize : a.natAbs+b.natAbs+2≤U) :
    (U:Int)+a<(V:Int)+b := by
  have hsep := entryRangeExponentialSeparation f B hf U V hU hV hUV
  have hp := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=U))
  have hdouble := Nat.mul_le_mul_left 2 hp
  have hexp : 2*(U+1)≤2^(U+1) := by
    rw [Nat.pow_succ]
    omega
  have ha : a≤(a.natAbs:Int) := Int.le_natAbs
  have hb : -b≤(b.natAbs:Int) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -b))
  omega

 theorem actualSignedOffsetComparison : Targets.ActualSignedOffsetComparison := by
  intro f B hf U V a b hU hV hsize
  constructor
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := offset_strict_order f B hf U V a b hU hV hlt (by omega)
      omega
    · have h := offset_strict_order f B hf V U b a hV hU hgt (by omega)
      omega
  · intro he
    subst V
    omega

 theorem outputOffsetFoundation : Targets.OutputOffsetFoundation :=
  ⟨properEntryRange,entryRangeExponentialSeparation,signedOffsetTailEffective,actualSignedOffsetComparison⟩

end LogicLineages.PermittedControl
