module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowNumericalProof
public import LogicLineages.OrdinalComparison.HeadEndpointProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeRow.Proof

private theorem actual_band (lam : Ordinal) (hl : lam<epsilonZero) (hs : Order.IsSuccLimit lam)
    (t : Nat) (ht : actualOrdinalNorm lam≤t) :
    actualHeadEndpoint lam t=Phi (predecessorIndex lam t) ∧
      Phi (predecessorIndex lam t)<actualHeadValue lam t ∧
      actualHeadValue lam t<2*Phi (predecessorIndex lam t) := by
  have hi := actualHeadInputFacts lam hl hs t ht
  have hb := actualInfiniteValueEndpointBand (actualHeadInitial lam t) hi.1 hi.2.1
  dsimp only at hb
  rw [hi.2.2] at hb
  change actualHeadEndpoint lam t=Phi (predecessorIndex lam t) ∧
    actualHeadEndpoint lam t<actualHeadValue lam t ∧
    actualHeadValue lam t<2*actualHeadEndpoint lam t ∧
    2*actualHeadEndpoint lam t<Phi (predecessorIndex lam t+1) at hb
  exact ⟨hb.1,hb.1 ▸ hb.2.1,hb.1 ▸ hb.2.2.1⟩

private theorem index_strict (lam : Ordinal) (hl : lam<epsilonZero) (hs : Order.IsSuccLimit lam)
    (t u : Nat) (ht : actualOrdinalNorm lam≤t) (hu : actualOrdinalNorm lam≤u) (htu : t<u) :
    predecessorIndex lam t<predecessorIndex lam u := by
  have he := (actualFixedHeadValueEndpointOrder lam hl hs t u ht hu htu).2
  rw [(actual_band lam hl hs t ht).1,(actual_band lam hl hs u hu).1] at he
  exact (Phi_strictMono.lt_iff_lt).mp he

private theorem index_mono (lam : Ordinal) (hl : lam<epsilonZero) (hs : Order.IsSuccLimit lam)
    (t u : Nat) (ht : actualOrdinalNorm lam≤t) (hu : actualOrdinalNorm lam≤u) (htu : t≤u) :
    predecessorIndex lam t≤predecessorIndex lam u := by
  rcases lt_or_eq_of_le htu with h | rfl
  · exact (index_strict lam hl hs t u ht hu h).le
  · exact le_rfl

private theorem numerical_mass (lam : Ordinal) (row : Row) :
    numericalMass (numerical lam row)=mass row := by
  simp only [numericalMass,numerical,mass,List.map_map,Function.comp_def]
private theorem numerical_threshold (lam : Ordinal) (K : Int) (row : Row) :
    numericalThreshold K (numerical lam row)=threshold K row := by
  rw [numericalThreshold,numerical_mass,threshold]
private theorem numerical_value (lam : Ordinal) (K : Int) (row : Row) :
    numericalValue K (numerical lam row)=value lam K row := by
  simp only [numericalValue,numerical,value,List.map_map,Function.comp_def]

theorem actualHeadDominance : Targets.ActualHeadDominance := by
  intro lam hl hs K row hp hdomain a ha hnon hmax
  have hpair : (numerical lam row).Pairwise (fun x y=>x.2.2≠y.2.2) := by
    rw [numerical,List.pairwise_map]
    apply List.Pairwise.imp_of_mem (p:=hp)
    intro x y hx hy hne heq
    have hxt := (hdomain x hx).1
    have hyt := (hdomain y hy).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (index_strict lam hl hs x.2 y.2 hxt hyt hlt)) heq
    · exact (ne_of_gt (index_strict lam hl hs y.2 x.2 hyt hxt hgt)) heq
  have hbands : ∀ b∈numerical lam row,
      numericalThreshold K (numerical lam row)≤b.2.2 ∧ Phi b.2.2<b.2.1 ∧ b.2.1<2*Phi b.2.2 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    have hcdom := hdomain c hc
    have hb := actual_band lam hl hs c.2 hcdom.1
    refine ⟨?_,hb.2⟩
    rw [numerical_threshold]
    exact hcdom.2.trans (iterate_self_le (fun x=>(self_lt_Phi x).le) _ _)
  have ham : (a.1,actualHeadValue lam a.2,predecessorIndex lam a.2)∈numerical lam row :=
    List.mem_map.mpr ⟨a,ha,rfl⟩
  have hgreat : ∀ b∈numerical lam row,
      b.2.2≤predecessorIndex lam a.2 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact index_mono lam hl hs c.2 a.2 (hdomain c hc).1 (hdomain a ha).1 (hmax c hc)
  have h := numericalDominance K (numerical lam row) hpair hbands
    (a.1,actualHeadValue lam a.2,predecessorIndex lam a.2) ham hnon hgreat
  rw [numerical_value] at h
  exact h
end LogicLineages.OrdinalComparison.CommonHeadLargeRow.Proof
