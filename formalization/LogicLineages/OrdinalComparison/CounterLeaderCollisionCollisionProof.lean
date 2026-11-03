module
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionSplitProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionExpansionProof
public import LogicLineages.OrdinalComparison.SameRankLeaderRecognitionProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderCollision.Proof
open CounterLeaderExpansion

private theorem member_le_sum (xs : List Nat) (x : Nat) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · simp only [List.sum_cons]
      omega
    · have h := ih hm
      simp only [List.sum_cons]
      omega

private theorem positive_actual_count (d a v : Nat) (hd : 0 < d) (hv : a+d+1 ≤ v) :
    0 < count d a v := by
  have hnorm : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
    simpa only [Nat.cast_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast hd
  have hdom : a + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) ≤ v := by
    rw [hnorm]
    omega
  exact (actualSuffixKernelTrace (d : Ordinal) hp (finiteOmegaPowerBelowEpsilonZero d)
    a v hdom).1

theorem actualCrossRankCollision : Targets.ActualCrossRankCollision := by
  intro k m c e t u ht hu heq
  have ht0 : threshold (m+k) c ≤ t := (Nat.le_max_left _ _).trans ht
  have hu0 : threshold m e ≤ u := (Nat.le_max_left _ _).trans hu
  obtain ⟨hc,hb⟩ := (CubicLeaderRecognition.Proof.actualLeaderRecognition
    (m+k) m c e t u ht hu).mp heq
  subst e
  obtain ⟨hes,hbs,hls,hge,hdom,hlen,hentries,hrs⟩ := exactChainSplitting k m c t ht0
  have hbottom : bottomInput m c (alignedInput k m c t) = bottomInput m c u := hbs.symm.trans hb
  have huA : u = alignedInput k m c t := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (SameRankLeaderRecognition.Proof.actualFixedRankStrictInputs
        m c u (alignedInput k m c t) hu0 hdom hlt).1) hbottom.symm
    · exact (ne_of_lt (SameRankLeaderRecognition.Proof.actualFixedRankStrictInputs
        m c (alignedInput k m c t) u hdom hu0 hgt).1) hbottom
  subst u
  have hi := (CounterLeaderExpansion.Proof.exactCounterLeaderIdentity (m+k) c t ht0).2.2
  have hj := (CounterLeaderExpansion.Proof.exactCounterLeaderIdentity m c (alignedInput k m c t) hdom).2.2
  have hsum : (residuals (m+k) c t).sum =
      (upperResiduals k m c t).sum + (residuals m c (alignedInput k m c t)).sum := by
    rw [hrs,List.sum_append]
  rw [hls] at hi
  have hdifference : (count (m+k+3) c t : Int) -
      (count (m+3) c (alignedInput k m c t) : Int) =
        ((upperResiduals k m c t).sum : Int) := by omega
  refine ⟨rfl,rfl,hdifference,?_⟩
  intro hk
  have hne : upperEntries k m c t ≠ [] := by
    intro hn
    rw [hn] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil (upperEntries k m c t) hne
  obtain ⟨hdegree,hupper,hin,hentry⟩ := hentries p hp
  have hpositive : 0 < count p.1 (c+p.1) p.2 :=
    positive_actual_count p.1 (c+p.1) p.2 (by omega) (by omega)
  have hm : count p.1 (c+p.1) p.2 ∈ upperResiduals k m c t := by
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hposSum := hpositive.trans_le (member_le_sum _ _ hm)
  exact ⟨hposSum,by omega⟩

end LogicLineages.OrdinalComparison.CounterLeaderCollision.Proof
