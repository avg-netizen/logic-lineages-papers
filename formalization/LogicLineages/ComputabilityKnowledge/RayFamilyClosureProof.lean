module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayFamilyClosure
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsEffectivity

@[expose] public section

/-! External heterogeneous-family closure proof after independent exact target
freeze. Original finite-map keys and literal structural raises are used; the
cross-height equality relation is not numerical functional equivalence. -/
namespace LogicLineages.ComputabilityKnowledge.RayFamilyClosureProof

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormProduct ExponentialNormalFormCodeOperations
open ExponentialNormalFormProof ExponentialNormalFormProductProof
open ExponentialNormalFormCodecProof ExponentialHereditaryCodecProof
open ExponentialNormalFormCodeOperationsProof RayFamilyClosure

theorem iteratedHeightTransport : Comparators.RayFamilyClosure.IteratedHeightTransport := by
  intro d h extra n
  induction extra with
  | zero => exact canonicalization d h n
  | succ extra ih =>
      have hr := heightTransportCodes d (h + extra) (raiseManyCode d h extra n)
      exact ⟨hr.1, hr.2.trans (congrArg (raiseForm (h + extra)) ih.2)⟩

theorem originalEmbeddingLaws : Comparators.RayFamilyClosure.OriginalEmbeddingLaws := by
  intro d h extra
  induction extra with
  | zero => exact ⟨Function.injective_id, fun _ => ⟨fun _ => rfl, rfl, id⟩⟩
  | succ extra ih =>
      refine ⟨(raise_injective (h + extra)).comp ih.1, ?_⟩
      intro f
      exact ⟨fun ρ => (raise_value (h + extra) _ ρ).trans ((ih.2 f).1 ρ),
        (raise_coeff (h + extra) _).trans (ih.2 f).2.1,
        fun hw => raise_wellFormed (h + extra) _ ((ih.2 f).2.2 hw)⟩

private theorem descendants_self (h n : Nat) : (h, n) ∈ descendants h n := by
  cases h <;> simp [descendants]

private theorem root_height (roots : List HeightCode) (p : HeightCode) (hp : p ∈ roots) :
    p.1 ≤ maxHeight roots := by
  induction roots with
  | nil => simp at hp
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_max_left _ _
      · exact (ih hp).trans (le_max_right _ _)

theorem originalMembersAndZero : Comparators.RayFamilyClosure.OriginalMembersAndZero := by
  intro d roots
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, descendants_self p.1 p.2⟩)
  · intro k hk
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨k, List.mem_range.mpr (by omega), rfl⟩)
  · simp [closedFamily, maxHeight]

private theorem raw_row_value (d : Nat) (es : MapCode) (hc : MapCanonical d es)
    (e : Nat × CoeffCode) (he : e ∈ es) : mapDecode d es e.1 = coeffDecode d e.2 := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
      obtain ⟨hp, hv⟩ := hc
      obtain ⟨hlt, hpair⟩ := List.pairwise_cons.mp hp
      have htail : MapCanonical d es := ⟨hpair, fun z hz => hv z (List.mem_cons_of_mem a hz)⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact head_eval (fun z hz => hlt z hz)
      · have hne : a.1 ≠ e.1 := Nat.ne_of_lt (hlt e he)
        change (Finsupp.single a.1 (coeffDecode d a.2) + mapDecode d es) e.1 = _
        simpa [Finsupp.single_apply, hne, Ne.symm hne] using ih htail he

private theorem row_support (d h : Nat) (es : MapCode) (hc : MapCanonical d es)
    (hkeys : ∀ e ∈ es, CodeCanonical d h e.1) (e : Nat × CoeffCode) (he : e ∈ es) :
    formDecode d h e.1 ∈ (entriesDecode d h es).support := by
  classical
  apply Finsupp.mem_support_iff.mpr
  rw [entriesDecode_mapDomain]
  rw [Finsupp.mapDomain_apply' {k | CodeCanonical d h k} (mapDecode d es)
    (support_canonical_keys d h es hkeys)
    (fun a ha b hb hab => (faithfulness d h a b ha hb).mp hab) (hkeys e he)]
  rw [raw_row_value d es hc e he]
  exact decode_ne_zero (hc.2 e he).2

private theorem descendants_valid (d h n : Nat) (hc : CodeCanonical d h n)
    (hw : WellFormed h (formDecode d h n)) (p : HeightCode) (hp : p ∈ descendants h n) :
    p.1 ≤ h ∧ CodeCanonical d p.1 p.2 ∧ WellFormed p.1 (formDecode d p.1 p.2) := by
  induction h generalizing n with
  | zero =>
      have hp' : p = (0, n) := by simpa [descendants] using hp
      subst p
      exact ⟨le_rfl, hc, hw⟩
  | succ h ih =>
      obtain ⟨es, rfl, hes, hkeys⟩ := hc
      simp only [descendants, parseEntries_encode, List.mem_cons, List.mem_flatMap] at hp
      rcases hp with rfl | ⟨e, he, hp⟩
      · exact ⟨le_rfl, ⟨es, rfl, hes, hkeys⟩, hw⟩
      · have hs := row_support d h es hes hkeys e he
        have hwkey := hw (formDecode d h e.1) (by simpa only [formDecode_succ_encode] using hs)
        have hb := ih e.1 (hkeys e he) hwkey.1 hp
        exact ⟨by omega, hb.2⟩

theorem closureBoundsAndValidity : Comparators.RayFamilyClosure.ClosureBoundsAndValidity := by
  intro d roots hroots p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    have hb := descendants_valid d q.1 q.2 (hroots q hq).1 (hroots q hq).2 p hp
    exact ⟨hb.1.trans (root_height roots q hq), hb.2⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hk' := List.mem_range.mp hk
    exact ⟨by omega, zeroCode_canonical d k,
      by rw [ExponentialHereditaryCodecProof.zeroCode_decode d k]; exact zero_wellFormed k⟩

private theorem descendants_trans (h n : Nat) (p q : HeightCode)
    (hp : p ∈ descendants h n) (hq : q ∈ descendants p.1 p.2) : q ∈ descendants h n := by
  induction h generalizing n with
  | zero =>
      have hp' : p = (0, n) := by simpa [descendants] using hp
      simpa [hp'] using hq
  | succ h ih =>
      simp only [descendants, List.mem_cons, List.mem_flatMap] at hp
      rcases hp with rfl | ⟨e, he, hp⟩
      · exact hq
      · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e, he, ih e.1 hp⟩)

private theorem descendants_zero (d k : Nat) :
    descendants k (zeroCode d k) = [(k, zeroCode d k)] := by
  cases k with
  | zero => rfl
  | succ k =>
      change (k + 1, zeroCode d (k + 1)) ::
        (parseEntries (Encodable.encode ([] : MapCode))).flatMap (fun e => descendants k e.1) = _
      rw [parseEntries_encode]
      rfl

private theorem closed_under_descendants (d : Nat) (roots : List HeightCode) (p q : HeightCode)
    (hp : p ∈ closedFamily d roots) (hq : q ∈ descendants p.1 p.2) :
    q ∈ closedFamily d roots := by
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨r, hr, hp⟩ := List.mem_flatMap.mp hp
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨r, hr, descendants_trans r.1 r.2 p q hp hq⟩)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hq' : q = (k, zeroCode d k) := by simpa only [descendants_zero, List.mem_singleton] using hq
    subst q
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩)

theorem actualSupportClosure : Comparators.RayFamilyClosure.ActualSupportClosure := by
  intro d roots hroots k n hn key hk
  classical
  have hdecode : formDecode d (k + 1) n = entriesDecode d k (parseEntries n) := rfl
  rw [hdecode, entriesDecode_mapDomain] at hk
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
  obtain ⟨e, he, rfl⟩ := mapDecode_support_key_mem d (parseEntries n) j hj
  refine ⟨e.1, ?_, heq⟩
  apply closed_under_descendants d roots (k + 1, n) (k, e.1) hn
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e, he, descendants_self k e.1⟩)

private theorem lift_properties (d H : Nat) (p : HeightCode) (hp : p.1 ≤ H)
    (hw : WellFormed p.1 (formDecode d p.1 p.2)) :
    CodeCanonical d H (liftCode d H p) ∧ WellFormed H (formDecode d H (liftCode d H p)) ∧
    (∀ ρ, value H (formDecode d H (liftCode d H p)) ρ = value p.1 (formDecode d p.1 p.2) ρ) ∧
    constantCoefficient H (formDecode d H (liftCode d H p)) =
      constantCoefficient p.1 (formDecode d p.1 p.2) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hp
  simp only [liftCode, Nat.add_sub_cancel_left]
  have ht := iteratedHeightTransport d p.1 extra p.2
  have hl := (originalEmbeddingLaws d p.1 extra).2 (formDecode d p.1 p.2)
  rw [ht.2]
  exact ⟨ht.1, hl.2.2 hw, hl.1, hl.2.1⟩

theorem liftedOriginalSemantics : Comparators.RayFamilyClosure.LiftedOriginalSemantics := by
  intro d roots hroots
  have hb := closureBoundsAndValidity d roots hroots
  constructor
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have hl := lift_properties d (maxHeight roots) p (hb p hp).1 (hb p hp).2.2
    exact ⟨hl.1, hl.2.1⟩
  · intro p hp
    have hl := lift_properties d (maxHeight roots) p (hb p hp).1 (hb p hp).2.2
    exact ⟨List.mem_map.mpr ⟨p, hp, rfl⟩, hl.2.2⟩

theorem sameHeightStructuralEquality : Comparators.RayFamilyClosure.SameHeightStructuralEquality := by
  intro d H h n m hh
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hh
  simp only [CommonHeightEqual, liftCode, Nat.add_sub_cancel_left,
    (iteratedHeightTransport d h extra n).2, (iteratedHeightTransport d h extra m).2]
  exact (originalEmbeddingLaws d h extra).1.eq_iff

theorem pr_raiseManyCode : Primrec (fun p : Nat × Nat × Nat × Nat =>
    raiseManyCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hd : Primrec (fun p : Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbase := pr_canonicalize.comp (hd.pair (hh.pair hn))
  have hstep : Primrec₂ (fun (p : Nat × Nat × Nat × Nat) (q : Nat × Nat) =>
      raiseCode p.1 (p.2.1 + q.1) q.2) := by
    exact (ExponentialNormalFormCodeOperationsEffectivity.pr_raiseCode.comp
      ((hd.comp Primrec.fst).pair ((Primrec.nat_add.comp (hh.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)))).to₂
  exact (Primrec.nat_rec' hk hbase hstep).of_eq (by
    rintro ⟨d, h, extra, n⟩
    induction extra with
    | zero => rfl
    | succ extra ih => simpa [raiseManyCode] using congrArg (raiseCode d (h + extra)) ih)

private def descendantChildren (p : HeightCode) : List HeightCode :=
  if p.1 = 0 then [] else (parseEntries p.2).map (fun e => (p.1 - 1, e.1))

private def descendantAssemble (p : HeightCode) (rs : List (List HeightCode)) : Option (List HeightCode) :=
  some (p :: rs.flatten)

theorem pr_descendants : Primrec (fun p : Nat × Nat => descendants p.1 p.2) := by
  have hchildren : Primrec descendantChildren := by
    apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const [])
    apply Primrec.list_map (pr_parseEntries.comp Primrec.snd)
    exact ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)).pair
      (Primrec.fst.comp Primrec.snd)).to₂
  have hassemble : Primrec₂ descendantAssemble :=
    (Primrec.option_some.comp (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_flatten.comp Primrec.snd))).to₂
  apply Primrec.nat_omega_rec' (fun p : HeightCode => descendants p.1 p.2)
    Primrec.fst hchildren hassemble
  · intro p q hq
    by_cases h0 : p.1 = 0
    · simp [descendantChildren, h0] at hq
    · have hm : q ∈ (parseEntries p.2).map (fun e => (p.1 - 1, e.1)) := by
        simpa only [descendantChildren, if_neg h0] using hq
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      dsimp
      omega
  · rintro ⟨h, n⟩
    cases h with
    | zero => rfl
    | succ h =>
        simp only [descendantChildren, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel, List.map_map, descendantAssemble, descendants]
        congr 2

theorem pr_maxHeight : Primrec maxHeight := by
  have hstep : Primrec₂ (fun (_ : List HeightCode) (q : HeightCode × Nat) => max q.1.1 q.2) :=
    (Primrec.nat_max.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

theorem pr_closedFamily : Primrec (fun p : Nat × List HeightCode => closedFamily p.1 p.2) := by
  have hroots : Primrec (fun p : Nat × List HeightCode =>
      p.2.flatMap (fun q => descendants q.1 q.2)) := by
    apply Primrec.list_flatMap Primrec.snd
    exact (pr_descendants.comp Primrec.snd).to₂
  have hz : Primrec (fun p : Nat × List HeightCode =>
      (List.range (maxHeight p.2 + 1)).map (fun h => (h, zeroCode p.1 h))) := by
    apply Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_add.comp (pr_maxHeight.comp Primrec.snd) (Primrec.const 1)))
    exact (Primrec.snd.pair (pr_zeroCode.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂
  exact Primrec.list_append.comp hroots hz

theorem pr_liftCode : Primrec (fun p : Nat × Nat × HeightCode => liftCode p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × Nat × HeightCode => p.1) := Primrec.fst
  have hH : Primrec (fun p : Nat × Nat × HeightCode => p.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun p : Nat × Nat × HeightCode => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : Nat × Nat × HeightCode => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact pr_raiseManyCode.comp (hd.pair (hh.pair ((Primrec.nat_sub.comp hH hh).pair hn)))

theorem pr_liftedFamily : Primrec (fun p : Nat × List HeightCode => liftedFamily p.1 p.2) := by
  apply Primrec.list_map pr_closedFamily
  exact (pr_liftCode.comp ((Primrec.fst.comp Primrec.fst).pair
    ((pr_maxHeight.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂

theorem actualUniformPrograms : Comparators.RayFamilyClosure.ActualUniformPrograms :=
  ⟨pr_raiseManyCode, pr_descendants, pr_maxHeight, pr_closedFamily, pr_liftCode, pr_liftedFamily⟩

theorem rayFamilyClosure : Comparators.RayFamilyClosure.Target :=
  ⟨iteratedHeightTransport, originalEmbeddingLaws, originalMembersAndZero,
    closureBoundsAndValidity, actualSupportClosure, liftedOriginalSemantics,
    sameHeightStructuralEquality, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.RayFamilyClosureProof
