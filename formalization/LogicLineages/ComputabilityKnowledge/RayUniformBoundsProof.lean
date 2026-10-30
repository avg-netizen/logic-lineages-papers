module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayUniformBounds
public import LogicLineages.ComputabilityKnowledge.RayCoefficientCollectionProof

@[expose] public section

/-! External proof after independently compiled target freeze. Uniform
structural bounds are proved on the original maps and literal code traversal;
no eventual comparison or exponent-gap hypothesis is used. -/
namespace LogicLineages.ComputabilityKnowledge.RayUniformBoundsProof

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialHereditaryCodecProof RayCoefficientCollection RayUniformBounds
open RayMapDifference RayFiniteSum

private theorem flatMap_member_length {α β : Type} (F : α → List β)
    (xs : List α) (x : α) (hx : x ∈ xs) : (F x).length ≤ (xs.flatMap F).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · have h := ih hx
        simp only [List.flatMap_cons, List.length_append]
        omega

private theorem rows_le_collection (h : Nat) (es : MapCode) :
    es.length ≤ (es.flatMap (fun e => e.2 :: coefficients h e.1)).length := by
  induction es with
  | nil => simp
  | cons e es ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem entries_width (d h : Nat) (es : MapCode) :
    (entriesDecode d h es).support.card ≤ es.length := by
  classical
  induction es with
  | nil => simp [entriesDecode]
  | cons e es ih =>
      change (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) +
        entriesDecode d h es).support.card ≤ _
      have hsingle : (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2)).support.card ≤ 1 :=
        (Finset.card_le_card Finsupp.support_single_subset).trans_eq (Finset.card_singleton _)
      have hadd := Finset.card_le_card (Finsupp.support_add (g₁ :=
        Finsupp.single (formDecode d h e.1) (coeffDecode d e.2)) (g₂ := entriesDecode d h es))
      have hunion := Finset.card_union_le
        (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2)).support
        (entriesDecode d h es).support
      simp only [List.length_cons]
      omega

private theorem width_mono {d h : Nat} {f : Form d h} {N M : Nat}
    (hNM : N ≤ M) (hf : HereditaryWidth h f N) : HereditaryWidth h f M := by
  induction h with
  | zero => trivial
  | succ h ih => exact ⟨hf.1.trans hNM, fun key hk => ih (hf.2 key hk)⟩

private theorem code_width (d h n : Nat) :
    HereditaryWidth h (formDecode d h n) (coefficients h n).length := by
  classical
  induction h generalizing n with
  | zero => trivial
  | succ h ih =>
      change (formDecode d (h + 1) n).support.card ≤ _ ∧ _
      have hdecode : formDecode d (h + 1) n = entriesDecode d h (parseEntries n) := rfl
      refine ⟨?_, ?_⟩
      · rw [hdecode]
        exact (entries_width d h (parseEntries n)).trans (rows_le_collection h (parseEntries n))
      · intro key hk
        rw [hdecode, entriesDecode_mapDomain] at hk
        obtain ⟨k, hks, heq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
        obtain ⟨e, he, rfl⟩ := mapDecode_support_key_mem d (parseEntries n) k hks
        rw [← heq]
        apply width_mono (N := (coefficients h e.1).length) _ (ih e.1)
        have hlen := flatMap_member_length (fun e : Nat × CoeffCode =>
          e.2 :: coefficients h e.1) (parseEntries n) e he
        simp only [List.length_cons] at hlen
        change (coefficients h e.1).length ≤
          ((parseEntries n).flatMap (fun e => e.2 :: coefficients h e.1)).length
        omega

theorem sourceBounds : Comparators.RayUniformBounds.SourceBounds := by
  intro d H ns hc
  constructor
  · intro n hn
    constructor
    · apply width_mono (N := (coefficients H n).length) _ (code_width d H n)
      have hlen := flatMap_member_length (coefficients H) ns n hn
      simp only [widthBound, collected, List.length_cons]
      omega
    · intro a ha
      exact Or.inr ⟨n, hn, ha⟩
  · intro k
    cases k with
    | zero => exact ⟨trivial, fun a ha => Or.inl ha⟩
    | succ k =>
        constructor
        · simp [HereditaryWidth, zeroForm]
        · intro a ha
          obtain ⟨key, hk, _⟩ := ha
          simp [zeroForm] at hk

theorem recursiveKeyBounds : Comparators.RayUniformBounds.RecursiveKeyBounds := by
  intro d H ns k f hw hc key hk
  exact ⟨hw.2 key hk, fun a ha => hc a ⟨key, hk, Or.inr ha⟩⟩

private theorem fold_member_bound {α : Type} (w : α → Nat) (xs : List α) (x : α)
    (hx : x ∈ xs) : w x ≤ xs.foldr (fun a acc => w a + acc) 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · have h := ih hx
        simp only [List.foldr_cons]
        omega

theorem actualAffineBound : Comparators.RayUniformBounds.ActualAffineBound := by
  intro d H ns hc a ha
  obtain ⟨c, hcm, rfl⟩ := RayCoefficientCollectionProof.literalCoverage d H ns hc a ha
  have hs := (AffineRayCalibrationProof.slopeCalibration d (collected H ns)).1 c
  have hv : affineSize d H ns (coeffDecode d c) =
      c.getD 0 0 + AffineRayCalibration.slope d (collected H ns) c := by
    dsimp only [affineSize, raySlope, sharedWeights]
    rw [hs]
    rfl
  rw [hv]
  exact fold_member_bound (fun c => c.getD 0 0 +
    AffineRayCalibration.slope d (collected H ns) c) (collected H ns) c hcm

private theorem coefficient_covered (d H : Nat) (ns : List Nat) (k : Nat)
    (f : Form d (k + 1)) (hf : Covered d H ns (k + 1) f) (key : Form d k) :
    FamilyCoefficient d H ns (f key) := by
  classical
  by_cases hk : key ∈ f.support
  · exact hf (f key) ⟨key, hk, Or.inl rfl⟩
  · exact Or.inl (Finsupp.notMem_support_iff.mp hk)

theorem actualMassBound : Comparators.RayUniformBounds.ActualMassBound := by
  intro d H ns hc k f g hf hg hfc hgc s hs
  classical
  let W := weightMass d H ns
  let N := widthBound H ns
  let weights : Fin d → Nat := fun i => (sharedWeights d H ns).getD i.val 0
  have hcard : s.card ≤ 2 * N := by
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le f.support g.support
    have h3 := hf.1
    have h4 := hg.1
    change s.card ≤ (f.support ∪ g.support).card at h1
    dsimp [N]
    omega
  have hcoeff : ∀ key : Form d k,
      (slopeDifference weights f g key).natAbs + (constantDifference f g key).natAbs ≤ 2 * W := by
    intro key
    have ha := actualAffineBound d H ns hc (f key) (coefficient_covered d H ns k f hfc key)
    have hb := actualAffineBound d H ns hc (g key) (coefficient_covered d H ns k g hgc key)
    have hA := Int.natAbs_sub_le (raySlope weights (f key) : Int) (raySlope weights (g key) : Int)
    have hC := Int.natAbs_sub_le (f key 0 : Int) (g key 0 : Int)
    simp only [Int.natAbs_natCast] at hA hC
    change f key 0 + raySlope weights (f key) ≤ W at ha
    change g key 0 + raySlope weights (g key) ≤ W at hb
    dsimp only [slopeDifference, constantDifference]
    omega
  calc
    coefficientMass s (slopeDifference weights f g) (constantDifference f g)
        ≤ ∑ key ∈ s, 2 * W := Finset.sum_le_sum (fun key _ => hcoeff key)
    _ = s.card * (2 * W) := by simp
    _ ≤ (2 * N) * (2 * W) := Nat.mul_le_mul_right _ hcard
    _ = massBound d H ns := by
      dsimp [massBound, N, W]
      calc
        (2 * widthBound H ns) * (2 * weightMass d H ns) =
            (2 * 2) * (widthBound H ns * weightMass d H ns) := by ac_rfl
        _ = 4 * widthBound H ns * weightMass d H ns := by simp [Nat.mul_assoc]

theorem commonDominanceThreshold : Comparators.RayUniformBounds.CommonDominanceThreshold := by
  intro d H ns hc
  refine ⟨le_max_left _ _, (le_max_left 4 _).trans (le_max_right _ _), ?_⟩
  intro k f g hf hg hfc hgc s hs
  have hmass := actualMassBound d H ns hc k f g hf hg hfc hgc s hs
  apply (max_le_max_left 4 (Nat.mul_le_mul_left 2 hmass)).trans
  exact le_max_right _ _

theorem pr_widthBound : Primrec (fun p : Nat × List Nat => widthBound p.1 p.2) :=
  Primrec.list_length.comp RayCoefficientCollectionProof.pr_collected

theorem pr_weightMass : Primrec (fun p : Nat × Nat × List Nat => weightMass p.1 p.2.1 p.2.2) := by
  let family : Nat × Nat × List Nat → List CoeffCode := fun p => collected p.2.1 p.2.2
  have hf : Primrec family := RayCoefficientCollectionProof.pr_collected.comp Primrec.snd
  have hstep : Primrec₂ (fun (p : Nat × Nat × List Nat) (q : CoeffCode × Nat) =>
      q.1.getD 0 0 + AffineRayCalibration.slope p.1 (family p) q.1 + q.2) := by
    apply Primrec.nat_add.comp
    · apply Primrec.nat_add.comp
      · exact (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
      · exact AffineRayCalibrationEffectivity.pr_slope.comp
          ((Primrec.fst.comp Primrec.fst).pair
            ((hf.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr hf (Primrec.const 0) hstep

theorem pr_massBound : Primrec (fun p : Nat × Nat × List Nat => massBound p.1 p.2.1 p.2.2) :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (pr_widthBound.comp Primrec.snd)) pr_weightMass

theorem pr_commonThreshold : Primrec (fun p : Nat × Nat × List Nat =>
    commonThreshold p.1 p.2.1 p.2.2) := by
  have hcut : Primrec (fun p : Nat × Nat × List Nat => sharedCutoff p.2.1 p.2.2) :=
    (RayCoefficientCollectionProof.actualUniformPrograms).2.2.2.comp Primrec.snd
  exact Primrec.nat_max.comp hcut (Primrec.nat_max.comp (Primrec.const 4)
    (Primrec.nat_mul.comp (Primrec.const 2) pr_massBound))

theorem actualUniformPrograms : Comparators.RayUniformBounds.ActualUniformPrograms :=
  ⟨pr_widthBound, pr_weightMass, pr_massBound, pr_commonThreshold⟩

theorem rayUniformBounds : Comparators.RayUniformBounds.Target :=
  ⟨sourceBounds, recursiveKeyBounds, actualAffineBound, actualMassBound,
    commonDominanceThreshold, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.RayUniformBoundsProof
