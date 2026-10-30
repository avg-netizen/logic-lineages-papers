module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayHeightInduction
public import LogicLineages.ComputabilityKnowledge.RayUniformBoundsProof
public import LogicLineages.ComputabilityKnowledge.RaySurvivingDifferenceProof
public import LogicLineages.ComputabilityKnowledge.RayStableMaximumProof
public import LogicLineages.ComputabilityKnowledge.RayFiniteSumProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof

@[expose] public section

/-! External source-height induction after exact target freeze. The induction
supplies the actual lower-key gaps; they are not assumed by the final target.
All bounds and the common ray are the previously proved literal programs. -/
namespace LogicLineages.ComputabilityKnowledge.RayHeightInductionProof

open ExponentialNormalForm ExponentialHereditaryCodec
open RayCoefficientCollection RayUniformBounds RayHeightInduction
open RayMapDifference RayFiniteSum RaySurvivingDifference RayStableMaximum RayDominance

noncomputable local instance formDecidableEq (d k : Nat) : DecidableEq (Form d k) := Classical.decEq _

private theorem threshold_positive (d H : Nat) (ns : List Nat) :
    0 < commonThreshold d H ns := by
  have h : 4 ≤ commonThreshold d H ns :=
    (le_max_left 4 _).trans (le_max_right _ _)
  omega

private theorem affine_order (d H : Nat) (ns : List Nat)
    (hc : ∀ n ∈ ns, CodeCanonical d H n) (a b : Affine d)
    (ha : FamilyCoefficient d H ns a) (hb : FamilyCoefficient d H ns b) (hab : a ≠ b) :
    OrderedAfter d H ns 0 a b ∨ OrderedAfter d H ns 0 b a := by
  have he := RayCoefficientCollectionProof.commonEventualComparison d H ns hc a b ha hb
  have hg := RayCoefficientCollectionProof.commonConstantFreeGap d H ns hc a b ha hb
  have hn : affineValue a (sharedRay d H ns (sharedCutoff H ns)) ≠
      affineValue b (sharedRay d H ns (sharedCutoff H ns)) := by
    intro h
    exact hab ((he _ le_rfl).1.mp h)
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · left
    intro t ht
    have hcut : sharedCutoff H ns ≤ t := (le_max_left _ _).trans ht
    exact ⟨(he t hcut).2.mpr hlt, fun ha0 hb0 => (hg ha0 hb0 hab t).1 hlt⟩
  · right
    intro t ht
    have hcut : sharedCutoff H ns ≤ t := (le_max_left _ _).trans ht
    have hne := (he t hcut).1
    have hnlt : ¬ affineValue a (sharedRay d H ns t) < affineValue b (sharedRay d H ns t) :=
      fun h => (Nat.not_lt_of_gt hgt) ((he t hcut).2.mp h)
    have hneq : affineValue a (sharedRay d H ns t) ≠ affineValue b (sharedRay d H ns t) :=
      fun h => hab (hne.mp h)
    exact ⟨by change affineValue b _ < affineValue a _; omega,
      fun hb0 ha0 => (hg ha0 hb0 hab t).2 (Nat.not_lt_of_gt hgt)⟩

private theorem coefficient_covered (d H : Nat) (ns : List Nat) (k : Nat)
    (f : Form d (k + 1)) (hf : Covered d H ns (k + 1) f) (key : Form d k) :
    FamilyCoefficient d H ns (f key) := by
  classical
  by_cases hk : key ∈ f.support
  · exact hf (f key) ⟨key, hk, Or.inl rfl⟩
  · exact Or.inl (Finsupp.notMem_support_iff.mp hk)

private theorem signed_affine (d : Nat) (weights : Fin d → Nat) (a b : Affine d) (t : Nat) :
    ((raySlope weights a : Int) - raySlope weights b) * t + ((a 0 : Int) - b 0) =
      (affineValue a (fun i => weights i * t) : Int) -
        affineValue b (fun i => weights i * t) := by
  rw [RayMapDifferenceProof.literalAffineRay d weights a t,
    RayMapDifferenceProof.literalAffineRay d weights b t]
  push_cast
  ring

private theorem difference_singleton (d H : Nat) (ns : List Nat) (k : Nat)
    (f g : Form d (k + 1)) (hs : survivingKeys f g = {zeroForm k}) (t : Nat) :
    (rayValue d H ns (k + 1) f t : Int) - rayValue d H ns (k + 1) g t =
      (rayValue d H ns 0 (f (zeroForm k)) t : Int) -
        rayValue d H ns 0 (g (zeroForm k)) t := by
  classical
  let weights : Fin d → Nat := fun i => (sharedWeights d H ns).getD i.val 0
  have he := RaySurvivingDifferenceProof.actualSurvivingSum d k f g weights t
  rw [hs] at he
  change (value (k + 1) f (fun i => weights i * t) : Int) -
      value (k + 1) g (fun i => weights i * t) =
      (affineValue (f (zeroForm k)) (fun i => weights i * t) : Int) -
        affineValue (g (zeroForm k)) (fun i => weights i * t)
  simpa only [lowerSum, Finset.sum_singleton, ExponentialNormalFormProof.zero_value,
    pow_zero, Nat.cast_one, mul_one, slopeDifference, constantDifference,
    signed_affine, rayValue, sharedRay, AffineRayCalibration.rayTuple,
    sharedWeights, value] using he

private theorem difference_split (d H : Nat) (ns : List Nat) (k : Nat)
    (f g : Form d (k + 1)) (e : Form d k) (he : e ∈ survivingKeys f g) (t : Nat) :
    (rayValue d H ns (k + 1) f t : Int) - rayValue d H ns (k + 1) g t =
      leadingValue
        ((slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g e) * t +
          constantDifference f g e)
        (rayValue d H ns k e t)
        (lowerSum ((survivingKeys f g).erase e)
          (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g)
          (constantDifference f g) (fun key => rayValue d H ns k key t) t) := by
  classical
  rw [show (rayValue d H ns (k + 1) f t : Int) - rayValue d H ns (k + 1) g t =
    lowerSum (survivingKeys f g)
      (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g)
      (constantDifference f g) (fun key => rayValue d H ns k key t) t from
        RaySurvivingDifferenceProof.actualSurvivingSum d k f g _ t]
  exact (Finset.add_sum_erase (survivingKeys f g)
    (fun key => (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g key *
      (t : Int) + constantDifference f g key) * ((2 ^ rayValue d H ns k key t : Nat) : Int)) he).symm

private theorem separation (d H : Nat) (ns : List Nat)
    (hc : ∀ n ∈ ns, CodeCanonical d H n) :
    ∀ k (f g : Form d k), WellFormed k f → WellFormed k g →
      HereditaryWidth k f (widthBound H ns) → HereditaryWidth k g (widthBound H ns) →
      Covered d H ns k f → Covered d H ns k g → f ≠ g →
      OrderedAfter d H ns k f g ∨ OrderedAfter d H ns k g f := by
  intro k
  induction k with
  | zero =>
      intro f g hf hg hfw hgw hfc hgc hne
      exact affine_order d H ns hc f g (hfc f rfl) (hgc g rfl) hne
  | succ k ih =>
      intro f g hf hg hfw hgw hfc hgc hne
      classical
      let T := commonThreshold d H ns
      let s := survivingKeys f g
      let v := fun key t => rayValue d H ns k key t
      have hT : 0 < T := threshold_positive d H ns
      have hprop : ∀ key ∈ s,
          WellFormed k key ∧ constantCoefficient k key = 0 ∧
          HereditaryWidth k key (widthBound H ns) ∧ Covered d H ns k key := by
        intro key hk
        have hwf := RaySurvivingDifferenceProof.actualLowerKeys d k f g hf hg key hk
        have hmem := ((RaySurvivingDifferenceProof.exactSurvivingSupport d k f g key).mp hk).1
        change key ∈ f.support ∪ g.support at hmem
        have hb : HereditaryWidth k key (widthBound H ns) ∧ Covered d H ns k key := by
          rcases Finset.mem_union.mp hmem with hm | hm
          · exact RayUniformBoundsProof.recursiveKeyBounds d H ns k f hfw hfc key hm
          · exact RayUniformBoundsProof.recursiveKeyBounds d H ns k g hgw hgc key hm
        exact ⟨hwf.1, hwf.2, hb⟩
      have hpairs : PairwiseGaps s v T := by
        intro a ha b hb hab
        have pa := hprop a ha
        have pb := hprop b hb
        rcases ih a b pa.1 pb.1 pa.2.2.1 pb.2.2.1 pa.2.2.2 pb.2.2.2 hab with ho | ho
        · exact Or.inl (fun t ht => (ho t ht).2 pa.2.1 pb.2.1)
        · exact Or.inr (fun t ht => (ho t ht).2 pb.2.1 pa.2.1)
      obtain ⟨e, he⟩ := RayStableMaximumProof.stableGreatestKey s v T
        ((RaySurvivingDifferenceProof.nonemptySurvivingSupport d k f g).mpr hne) hpairs
      have hmax : max T 1 = T := max_eq_left (by omega)
      rw [hmax] at he
      have pe := hprop e he.1
      have hcoeffne := ((RaySurvivingDifferenceProof.exactSurvivingSupport d k f g e).mp he.1).2
      have hcoefforder := affine_order d H ns hc (f e) (g e)
        (coefficient_covered d H ns k f hfc e) (coefficient_covered d H ns k g hgc e) hcoeffne
      by_cases hezero : e = zeroForm k
      · have hs : s = {zeroForm k} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hezero ▸ he.1, ?_⟩
          intro a ha
          exact RayStableMaximumProof.zeroGreatestCase s v T (zeroForm k) hT
            (fun t => ExponentialNormalFormProof.zero_value k _) (hezero ▸ he) a ha
        have hd := difference_singleton d H ns k f g hs
        rw [hezero] at hcoefforder
        rcases hcoefforder with ho | ho
        · left
          intro t ht
          have ha := ho t ht
          have hdiff := hd t
          refine ⟨by omega, ?_⟩
          intro hf0 hg0
          have hgap := ha.2 hf0 hg0
          omega
        · right
          intro t ht
          have ha := ho t ht
          have hdiff := hd t
          refine ⟨by omega, ?_⟩
          intro hg0 hf0
          have hgap := ha.2 hg0 hf0
          omega
      · have hz := (RayUniformBoundsProof.sourceBounds d H ns hc).2 k
        have hE : ∀ t, T ≤ t → t ≤ v e t := by
          rcases ih e (zeroForm k) pe.1 (ExponentialNormalFormProof.zero_wellFormed k)
              pe.2.2.1 hz.1 pe.2.2.2 hz.2 hezero with ho | ho
          · have hb := (ho T le_rfl).1
            have hzero : rayValue d H ns k (zeroForm k) T = 0 :=
              ExponentialNormalFormProof.zero_value k _
            omega
          · intro t ht
            have hb := (ho t ht).2 (ExponentialNormalFormProof.zero_coeff k) pe.2.1
            have hzero : rayValue d H ns k (zeroForm k) t = 0 :=
              ExponentialNormalFormProof.zero_value k _
            dsimp [v]
            omega
        have herase : s.erase e ⊆ keySet f g := by
          intro key hk
          exact ((RaySurvivingDifferenceProof.exactSurvivingSupport d k f g key).mp
            (Finset.mem_of_mem_erase hk)).1
        have hthreshold := (RayUniformBoundsProof.commonDominanceThreshold d H ns hc).2.2
          k f g hfw hgw hfc hgc (s.erase e) herase
        have hsign : ∀ t, T ≤ t →
            (0 < slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g e *
                (t : Int) + constantDifference f g e →
              (t : Int) ≤ (rayValue d H ns (k + 1) f t : Int) - rayValue d H ns (k + 1) g t) ∧
            (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g e *
                (t : Int) + constantDifference f g e < 0 →
              (rayValue d H ns (k + 1) f t : Int) - rayValue d H ns (k + 1) g t ≤ -(t : Int)) := by
          intro t ht
          have hgap : ∀ key ∈ s.erase e, v key t + t ≤ v e t := by
            intro key hk
            exact he.2 key (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) t ht
          have hb := RayFiniteSumProof.actualLeadingTermSign (s.erase e)
            (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g)
            (constantDifference f g) (fun key => v key t) t (v e t)
            (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g e *
              (t : Int) + constantDifference f g e) (hthreshold.trans ht) (hE t ht) hgap
          dsimp only [v, s] at hb
          rw [← difference_split d H ns k f g e he.1 t] at hb
          exact hb
        have hlinear : ∀ t : Nat,
            slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g e *
              (t : Int) + constantDifference f g e =
              (rayValue d H ns 0 (f e) t : Int) - rayValue d H ns 0 (g e) t :=
          fun t => signed_affine d _ (f e) (g e) t
        rcases hcoefforder with ho | ho
        · left
          intro t ht
          have htpos : 0 < t := lt_of_lt_of_le hT ht
          have ha := (ho t ht).1
          have hlin := hlinear t
          have hdiff := (hsign t ht).2 (by omega)
          exact ⟨by omega, fun _ _ => by omega⟩
        · right
          intro t ht
          have htpos : 0 < t := lt_of_lt_of_le hT ht
          have ha := (ho t ht).1
          have hlin := hlinear t
          have hdiff := (hsign t ht).1 (by omega)
          exact ⟨by omega, fun _ _ => by omega⟩

theorem stableEqualityAndOrder : Comparators.RayHeightInduction.StableEqualityAndOrder := by
  intro d H ns hc hw n hn m hm t ht
  have hb := (RayUniformBoundsProof.sourceBounds d H ns hc).1
  by_cases heq : formDecode d H n = formDecode d H m
  · simp [heq]
  · rcases separation d H ns hc H _ _ (hw n hn) (hw m hm)
      (hb n hn).1 (hb m hm).1 (hb n hn).2 (hb m hm).2 heq with ho | ho
    · have h1 := (ho t ht).1
      have h2 := (ho (commonThreshold d H ns) le_rfl).1
      exact ⟨⟨fun h => False.elim ((Nat.ne_of_lt h1) h), fun h => False.elim (heq h)⟩,
        ⟨fun _ => h2, fun _ => h1⟩⟩
    · have h1 := (ho t ht).1
      have h2 := (ho (commonThreshold d H ns) le_rfl).1
      exact ⟨⟨fun h => False.elim ((Nat.ne_of_gt h1) h), fun h => False.elim (heq h)⟩,
        by constructor <;> intro h <;> omega⟩

theorem constantFreeOrientedGap : Comparators.RayHeightInduction.ConstantFreeOrientedGap := by
  intro d H ns hc hw n hn m hm hn0 hm0 hne t ht
  have hb := (RayUniformBoundsProof.sourceBounds d H ns hc).1
  rcases separation d H ns hc H _ _ (hw n hn) (hw m hm)
    (hb n hn).1 (hb m hm).1 (hb n hn).2 (hb m hm).2 hne with ho | ho
  · have hT := (ho (commonThreshold d H ns) le_rfl).1
    exact ⟨fun _ => (ho t ht).2 hn0 hm0, fun h => False.elim (h hT)⟩
  · have hT := (ho (commonThreshold d H ns) le_rfl).1
    exact ⟨fun h => by omega, fun _ => (ho t ht).2 hm0 hn0⟩

theorem rayHeightInduction : Comparators.RayHeightInduction.Target :=
  ⟨stableEqualityAndOrder, constantFreeOrientedGap⟩

end LogicLineages.ComputabilityKnowledge.RayHeightInductionProof
