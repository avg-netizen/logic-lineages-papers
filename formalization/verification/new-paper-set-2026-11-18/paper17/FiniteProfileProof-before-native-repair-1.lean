module
public import LogicLineages.PermittedControl.FiniteProfileTargets
public import LogicLineages.PermittedControl.RelativeNormProof
public import LogicLineages.OrdinalComparison.RawComparisonProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private def syntaxProfile (e : Nat) : ONote → Nat
  | .zero => 0
  | .oadd a c t =>
    (if rawComparisonCode e (rawNoteEncode a) = 2 then 0
     else (c : Nat)*(1+Vendor.R1.treeWeight a)) + syntaxProfile e t

private theorem profile_table_length (e n : Nat) : (rawProfileTable e n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rawProfileTable,List.length_append,List.length_singleton,ih]

private theorem profile_table_correct (e n : Nat) : ∀ k ≤ n,
    (rawProfileTable e n).getD k 0 = syntaxProfile e (rawNoteDecode k) := by
  induction n with
  | zero =>
    intro k hk
    have : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · rw [rawProfileTable,List.getD_append _ _ _ _ (by rw [profile_table_length]; omega)]
      exact ih k hkn
    · have he : k=n+1 := by omega
      subst k
      rw [rawProfileTable,List.getD_append_right _ _ _ _ (by rw [profile_table_length])]
      simp only [profile_table_length,Nat.sub_self,List.getD_cons_zero]
      rw [ih _ ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)),rawNoteDecode,syntaxProfile,
        rawNoteEncodeDecode]
      rw [← rawNormCodeCorrect (rawNoteDecode n.unpair.1),rawNoteEncodeDecode]

private theorem profile_code_syntax (e : Nat) (mu : ONote) :
    rawProfileCode (rawNoteEncode mu) e = syntaxProfile e mu := by
  rw [rawProfileCode,profile_table_correct e _ _ le_rfl,rawNoteDecodeEncode]

private theorem syntax_profile_actual (mu : ONote) (hm : ONote.NF mu) (e : NONote) :
    syntaxProfile (rawNoteEncode e.1) mu = relativeProfile mu.repr e.1.repr := by
  rw [(relativePrefixNorm mu.repr e.1.repr (normalRepresentationSound ⟨mu,hm⟩)).2.1]
  induction mu with
  | zero => simp [syntaxProfile,ONote.repr]
  | oadd a c t iha iht =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd a c t).repr =
        (a.repr,((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc (Ordinal.natCast_lt_omega0 _) hm.snd'.repr_lt
    have hcmp := (rawComparisonOrdinalCorrect e ⟨a,hm.fst⟩).2.2
    have hnorm := actualOrdinalNorm_notationCorrespondence (⟨a,hm.fst⟩ : NONote)
    rw [syntaxProfile,hcnf]
    by_cases he : e.1.repr ≤ a.repr
    · have hn : rawComparisonCode (rawNoteEncode e.1) (rawNoteEncode a) ≠ 2 :=
        fun h => (not_lt_of_ge he) (hcmp.mp h)
      simp only [hn,↓reduceIte,List.filter_cons,he,decide_true,Bool.true_eq_true,
        List.map_cons,List.sum_cons]
      rw [← iht hm.snd]
      simpa only [hnorm,Ordinal.card_nat,Cardinal.toNat_natCast]
    · have hc' : rawComparisonCode (rawNoteEncode e.1) (rawNoteEncode a)=2 := hcmp.mpr (lt_of_not_ge he)
      simp only [hc',↓reduceIte,zero_add,List.filter_cons,he,decide_false,Bool.false_eq_true]
      exact iht hm.snd

 theorem rawProfileCorrect : Targets.RawProfileCorrect := by
  intro mu e
  rw [profile_code_syntax]
  exact syntax_profile_actual mu.1 mu.2 e

 theorem rawProfileEffective : Targets.RawProfileEffective := by
  let step : Nat → Nat × List Nat → List Nat := fun e p => p.2 ++ [
    (if rawComparisonCode e p.1.unpair.1 = 2 then 0
     else (p.1.unpair.2.unpair.1+1)*(1+rawNormCode p.1.unpair.1))+
      p.2.getD p.1.unpair.2.unpair.2 0]
  have hn : Primrec (fun p : Nat × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha := Primrec.fst.comp (Primrec.unpair.comp hn)
  have hr := Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hn))
  have hc := Primrec.succ.comp (Primrec.fst.comp hr)
  have hb := Primrec.snd.comp hr
  have hcmp := rawComparisonPrimitiveRecursive.comp Primrec.fst ha
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp ha
  have hval := Primrec.nat_mul.comp hc (Primrec.nat_add.comp (Primrec.const 1) hnorm)
  have hif := Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 2)) (Primrec.const 0) hval
  have hsum := Primrec.nat_add.comp hif ((Primrec.list_getD 0).comp ht hb)
  have hstep : Primrec₂ step := Primrec.list_concat.comp ht hsum
  have htable : Primrec₂ rawProfileTable := (Primrec.nat_rec (Primrec.const [0]) hstep).of_eq (by
    intro e n
    induction n with
    | zero => rfl
    | succ n ih => change step e (n,_) = _; rw [ih]; rfl)
  exact (Primrec.list_getD 0).comp (htable.comp Primrec.snd Primrec.fst) Primrec.fst

 theorem jointProfilePieceConstant : Targets.JointProfilePieceConstant := by
  intro mu nu x y hmu hnu hp
  have hweights : ∀ a : Ordinal.{0}, a < epsilonZero →
      (∀ b ∈ (Ordinal.CNF Ordinal.omega0 a).map Prod.fst, (x ≤ b ↔ y ≤ b)) →
      relativeProfile a x = relativeProfile a y := by
    intro a ha h
    rw [(relativePrefixNorm a x ha).2.1,(relativePrefixNorm a y ha).2.1]
    congr 2
    apply List.filter_congr
    intro p hp
    exact congrArg decide (propext (h p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  constructor
  · apply hweights mu hmu
    intro b hb
    exact hp b (List.mem_append_left _ hb)
  · apply hweights nu hnu
    intro b hb
    exact hp b (List.mem_append_right _ hb)

 theorem jointProfileFiniteCover : Targets.JointProfileFiniteCover := by
  classical
  intro mu nu E x hmu hnu hE hx hxE
  let l := jointProfileBreakpoints mu nu
  let s := l.toFinset.filter (fun b => b < x)
  by_cases hs : s.Nonempty
  · let b := s.max' hs
    have hb : b ∈ s := Finset.max'_mem s hs
    have hbl : b ∈ l := List.mem_toFinset.mp (Finset.mem_filter.mp hb).1
    have hbx : b < x := (Finset.mem_filter.mp hb).2
    let y := max (2 : Ordinal) (b+1)
    have hyx : y ≤ x := max_le hx (Order.add_one_le_iff.mpr hbx)
    have hyE : y < E := hyx.trans_lt hxE
    have h2y : 2 ≤ y := le_max_left _ _
    have hymem : y ∈ jointProfileRepresentatives mu nu E := by
      apply List.mem_filter.mpr
      refine ⟨?_, by simpa using And.intro h2y hyE⟩
      by_cases h : b+1 ≤ (2 : Ordinal)
      · have hy : y=2 := max_eq_left h
        rw [hy]
        exact List.mem_cons_self
      · have hy : y=b+1 := max_eq_right (le_of_not_ge h)
        rw [hy]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨b,hbl,rfl⟩))
    refine ⟨y,hymem,?_⟩
    intro z hz
    constructor
    · intro hxz
      exact hyx.trans hxz
    · intro hyz
      by_contra h
      have hzS : z ∈ s := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hz,lt_of_not_ge h⟩
      have hzb : z ≤ b := Finset.le_max' s z hzS
      have hby : b < y := (Order.lt_add_one_iff.mpr le_rfl).trans_le (le_max_right _ _)
      exact (not_lt_of_ge (hyz.trans hzb)) hby
  · refine ⟨2,?_,?_⟩
    · apply List.mem_filter.mpr
      exact ⟨List.mem_cons_self,by simpa using And.intro le_rfl (hx.trans_lt hxE)⟩
    · intro z hz
      have hxz : x ≤ z := by
        by_contra h
        exact hs ⟨z,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hz,lt_of_not_ge h⟩⟩
      exact ⟨fun _ => hx.trans hxz,fun _ => hxz⟩

 theorem finiteProfileFoundation : Targets.FiniteProfileFoundation :=
  ⟨rawProfileCorrect,rawProfileEffective,jointProfilePieceConstant,jointProfileFiniteCover⟩

end LogicLineages.PermittedControl
