module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayCoefficientCollection
public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof
public import LogicLineages.ComputabilityKnowledge.AffineRayCalibrationProof

@[expose] public section

/-! External continuation, independently authored after the exact target was
reviewed, compiled, and frozen. This proves coefficient collection and shared
affine calibration, not the still separate higher-height ray induction. -/
namespace LogicLineages.ComputabilityKnowledge.RayCoefficientCollectionProof

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormCodecProof ExponentialHereditaryCodecProof
open RayCoefficientCollection AffineRayCalibration

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

private theorem decoded_row (d h : Nat) (es : MapCode) (hc : MapCanonical d es)
    (hkeys : ∀ e ∈ es, CodeCanonical d h e.1) (key : Form d h)
    (hk : key ∈ (entriesDecode d h es).support) :
    ∃ e ∈ es, formDecode d h e.1 = key ∧
      entriesDecode d h es key = coeffDecode d e.2 := by
  classical
  rw [entriesDecode_mapDomain] at hk
  obtain ⟨k, hks, heq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
  obtain ⟨e, he, rfl⟩ := mapDecode_support_key_mem d es k hks
  refine ⟨e, he, heq, ?_⟩
  rw [entriesDecode_mapDomain, ← heq]
  rw [Finsupp.mapDomain_apply' {k | CodeCanonical d h k} (mapDecode d es)
    (support_canonical_keys d h es hkeys)
    (fun a ha b hb hab => (faithfulness d h a b ha hb).mp hab) (hkeys e he)]
  exact raw_row_value d es hc e he

private theorem coefficient_coverage (d h n : Nat) (hc : CodeCanonical d h n)
    (a : Affine d) (ha : CoefficientOccurs h (formDecode d h n) a) :
    ∃ c ∈ coefficients h n, coeffDecode d c = a := by
  induction h generalizing n with
  | zero =>
      refine ⟨parseCoefficients n, by simp [coefficients], ?_⟩
      exact ha.symm
  | succ h ih =>
      obtain ⟨es, rfl, hes, hkeys⟩ := hc
      obtain ⟨key, hk, ha⟩ := ha
      rw [formDecode_succ_encode] at hk
      obtain ⟨e, he, heq, hcoeff⟩ := decoded_row d h es hes hkeys key hk
      rcases ha with ha | ha
      · refine ⟨e.2, ?_, ?_⟩
        · simp only [coefficients, parseEntries_encode, List.mem_flatMap]
          exact ⟨e, he, List.mem_cons_self⟩
        · rw [formDecode_succ_encode] at ha
          exact hcoeff.symm.trans ha.symm
      · rw [← heq] at ha
        obtain ⟨c, hcm, hca⟩ := ih e.1 (hkeys e he) ha
        refine ⟨c, ?_, hca⟩
        simp only [coefficients, parseEntries_encode, List.mem_flatMap]
        exact ⟨e, he, List.mem_cons_of_mem e.2 hcm⟩

theorem literalCoverage : Comparators.RayCoefficientCollection.LiteralCoverage := by
  intro d h ns hc a ha
  rcases ha with rfl | ⟨n, hn, ha⟩
  · exact ⟨[], by simp [collected], by ext i; simp [coeffDecode]⟩
  · obtain ⟨c, hcm, hca⟩ := coefficient_coverage d h n (hc n hn) a ha
    exact ⟨c, List.mem_cons_of_mem [] (List.mem_flatMap.mpr ⟨n, hn, hcm⟩), hca⟩

theorem commonPositiveRay : Comparators.RayCoefficientCollection.CommonPositiveRay := by
  intro d h ns
  obtain ⟨hbase, hlen, hcut, hweights, hbound⟩ :=
    AffineRayCalibrationBasics.positiveCalibration d (collected h ns)
  refine ⟨hlen, hcut, fun i => ⟨(hweights i).2, ?_⟩⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le hcut ht
  exact Nat.mul_pos (hweights i).2 htpos

theorem commonSlopeInjection : Comparators.RayCoefficientCollection.CommonSlopeInjection := by
  intro d h ns hc a b ha hb
  obtain ⟨ca, hca, rfl⟩ := literalCoverage d h ns hc a ha
  obtain ⟨cb, hcb, rfl⟩ := literalCoverage d h ns hc b hb
  have h := AffineRayCalibrationProof.slopeCalibration d (collected h ns)
  simpa only [sharedWeights, ← h.1 ca, ← h.1 cb] using
    h.2 ca (List.mem_cons_of_mem [] hca) cb (List.mem_cons_of_mem [] hcb)

theorem commonEventualComparison : Comparators.RayCoefficientCollection.CommonEventualComparison := by
  intro d h ns hc a b ha hb t ht
  obtain ⟨ca, hca, rfl⟩ := literalCoverage d h ns hc a ha
  obtain ⟨cb, hcb, rfl⟩ := literalCoverage d h ns hc b hb
  have H := AffineRayCalibrationProof.computedEventualComparison d (collected h ns)
    ca (List.mem_cons_of_mem [] hca) cb (List.mem_cons_of_mem [] hcb)
  have Ht := H t ht
  have HN := H (sharedCutoff h ns) (Nat.le_refl _)
  exact ⟨Ht.2.1, Ht.1.symm.trans HN.1⟩

theorem commonConstantFreeGap : Comparators.RayCoefficientCollection.CommonConstantFreeGap := by
  intro d h ns hc a b ha hb ha0 hb0 hab t
  obtain ⟨ca, hca, rfl⟩ := literalCoverage d h ns hc a ha
  obtain ⟨cb, hcb, rfl⟩ := literalCoverage d h ns hc b hb
  have H := AffineRayCalibrationProof.constantFreeGap d (collected h ns)
    ca (List.mem_cons_of_mem [] hca) cb (List.mem_cons_of_mem [] hcb) ha0 hb0 hab t
  have HN := AffineRayCalibrationProof.computedEventualComparison d (collected h ns)
    ca (List.mem_cons_of_mem [] hca) cb (List.mem_cons_of_mem [] hcb)
    (sharedCutoff h ns) (Nat.le_refl _)
  refine ⟨fun hlt => H.1 (HN.1.mpr hlt), fun hnlt => H.2 ?_⟩
  cases hv : rayCompare d (collected h ns) ca cb with
  | false => rfl
  | true => exact False.elim (hnlt (HN.1.mp hv))

private def assembleCollections (es : MapCode) (rs : List (List CoeffCode)) :
    List CoeffCode :=
  ((List.range es.length).map (fun i => (es.getD i (0, [])).2 :: rs.getD i [])).flatten

private theorem pr_assembleCollections :
    Primrec (fun p : MapCode × List (List CoeffCode) => assembleCollections p.1 p.2) := by
  unfold assembleCollections
  apply Primrec.list_flatten.comp
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
  exact (Primrec.list_cons.comp
    (Primrec.snd.comp ((Primrec.list_getD (0, ([] : CoeffCode))).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂

private theorem assembleCollections_map (es : MapCode) (F : Nat × CoeffCode → List CoeffCode) :
    assembleCollections es (es.map F) = es.flatMap (fun e => e.2 :: F e) := by
  have h : (List.range es.length).map (fun i =>
      (es.getD i (0, [])).2 :: (es.map F).getD i []) = es.map (fun e => e.2 :: F e) := by
    apply List.ext_getElem
    · simp
    · intro i hleft hright
      have hi : i < es.length := by simpa using hright
      simp [hi]
  unfold assembleCollections
  rw [h]
  clear h
  induction es with
  | nil => rfl
  | cons e es ih => simpa using congrArg (fun xs => (e.2 :: F e) ++ xs) ih

theorem pr_coefficients : Primrec (fun p : Nat × Nat => coefficients p.1 p.2) := by
  let f : Nat × Nat → List CoeffCode := fun p => coefficients p.1 p.2
  let children : Nat × Nat → List (Nat × Nat) := fun p =>
    if p.1 = 0 then [] else (parseEntries p.2).map (fun e => (p.1 - 1, e.1))
  let assemble : Nat × Nat → List (List CoeffCode) → Option (List CoeffCode) := fun p rs =>
    some (if p.1 = 0 then [parseCoefficients p.2]
      else assembleCollections (parseEntries p.2) rs)
  have hchildren : Primrec children := by
    apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const [])
    apply Primrec.list_map (pr_parseEntries.comp Primrec.snd)
    exact ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)).pair
      (Primrec.fst.comp Primrec.snd)).to₂
  have hassemble : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
    · exact Primrec.list_cons.comp
        (pr_parseCoefficients.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const [])
    · exact pr_assembleCollections.comp
        ((pr_parseEntries.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  apply Primrec.nat_omega_rec' f Primrec.fst hchildren hassemble
  · intro p q hq
    by_cases h0 : p.1 = 0
    · simp [children, h0] at hq
    · have hmap : q ∈ (parseEntries p.2).map (fun e => (p.1 - 1, e.1)) := by
        simpa only [children, if_neg h0] using hq
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmap
      dsimp
      omega
  · rintro ⟨h, n⟩
    cases h with
    | zero => rfl
    | succ h => simp [children, assemble, f, coefficients, List.map_map, assembleCollections_map]

theorem pr_collected : Primrec (fun p : Nat × List Nat => collected p.1 p.2) := by
  apply Primrec.list_cons.comp (Primrec.const [])
  apply Primrec.list_flatMap Primrec.snd
  exact (pr_coefficients.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem actualUniformPrograms : Comparators.RayCoefficientCollection.ActualUniformPrograms := by
  refine ⟨pr_coefficients, pr_collected, ?_, ?_⟩
  · exact AffineRayCalibrationEffectivity.pr_weights.comp
      (Primrec.fst.pair (pr_collected.comp Primrec.snd))
  · exact AffineRayCalibrationEffectivity.pr_cutoff.comp pr_collected

theorem rayCoefficientCollection : Comparators.RayCoefficientCollection.Target :=
  ⟨literalCoverage, commonPositiveRay, commonSlopeInjection, commonEventualComparison,
    commonConstantFreeGap, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.RayCoefficientCollectionProof
