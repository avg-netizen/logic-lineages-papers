module
public import LogicLineages.OrdinalComparison.SparseSignedCollectedTargets
public import LogicLineages.OrdinalComparison.SparseSignedNumericalProof
public import LogicLineages.OrdinalComparison.CollectedPeakProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualCollectedTagPeakIndexCalibration : Targets.ActualCollectedTagPeakIndexCalibration := by
  intro rho A hl he hA ho x hx
  let a := actualCollectedTagInput rho A x
  have hf := actualFiniteTailClosureNorm rho.1.repr he (actualCollectedPositiveEval A x)
  have hae : a<epsilonZero := hf.1
  have han : Ordinal.omega0≤a := (Ordinal.omega0_le_of_isSuccLimit hl).trans le_self_add
  have hnorm : x≤actualOrdinalNorm a := by
    have hv := collectedPositiveInputLower A hA ho x
    change x≤actualOrdinalNorm (rho.1.repr+(actualCollectedPositiveEval A x : Ordinal))
    rw [hf.2]
    omega
  have hp := actualSparsePeaks a hae han (hx.trans hnorm)
  have hi := iterate_self_le (fun n => (self_lt_Phi n).le)
    (actualReplacementCount a-1) (actualOrdinalNorm a)
  have hs : x≤actualCollectedTagPeakIndex rho A x := hnorm.trans hi
  have hz : actualCollectedTagPeak rho A x=Phi (actualCollectedTagPeakIndex rho A x) := hp.2.2.1
  refine ⟨hs,hz,?_⟩
  have hlo := hp.2.2.2.1
  have hhi := hp.2.2.2.2.2.1
  change actualCollectedTagPeak rho A x<actualProfileHead rho (actualCollectedPositiveEval A x) at hlo
  change actualProfileHead rho (actualCollectedPositiveEval A x)<2*actualCollectedTagPeak rho A x at hhi
  rw [hz] at hlo hhi
  exact ⟨hlo,hhi⟩

private theorem mapped_pairwise {α β : Type} (f : α → β) (R : α → α → Prop) (S : β → β → Prop)
    (l : List α) (hp : l.Pairwise R)
    (h : ∀ a∈l, ∀ b∈l, R a b → S (f a) (f b)) : (l.map f).Pairwise S := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hd := List.pairwise_cons.mp hp
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb
      rcases List.mem_map.mp hb with ⟨c,hc,rfl⟩
      exact h a List.mem_cons_self c (List.mem_cons_of_mem a hc) (hd.1 c hc)
    · exact ih hd.2 (fun a ha b hb hr => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hr)

theorem sparseSignedCollectedNonzero : Targets.SparseSignedCollectedNonzero := by
  intro row p q x hv hn hp hx
  have hx2 : 2≤x := by
    have h4 : 4≤x := (le_max_left _ _).trans hx
    omega
  let f : ((NONote × CollectedPositiveNF) × Int) → Int × Nat × Nat := fun entry =>
    (entry.2,actualProfileHead entry.1.1 (actualCollectedPositiveEval entry.1.2 x),
      actualCollectedTagPeakIndex entry.1.1 entry.1.2 x)
  have hcal : ∀ entry∈row,
      x≤(f entry).2.2 ∧ actualCollectedTagPeak entry.1.1 entry.1.2 x=Phi (f entry).2.2 ∧
      Phi (f entry).2.2<(f entry).2.1 ∧ (f entry).2.1<2*Phi (f entry).2.2 := by
    intro entry hm
    have hd := hv.2 entry hm
    exact actualCollectedTagPeakIndexCalibration entry.1.1 entry.1.2 hd.2.1 hd.2.2.1
      hd.2.2.2.1 hd.2.2.2.2 x hx2
  have hn' : row.map f≠[] := by simpa using hn
  have hv' : ∀ entry∈row.map f, entry.1≠0 ∧ x≤entry.2.2 ∧
      Phi entry.2.2<entry.2.1 ∧ entry.2.1<2*Phi entry.2.2 := by
    intro entry hm
    rcases List.mem_map.mp hm with ⟨a,ha,rfl⟩
    have hc := hcal a ha
    exact ⟨(hv.2 a ha).1,hc.1,hc.2.2⟩
  have hp' : (row.map f).Pairwise (fun a b => a.2.2≠b.2.2) := by
    apply mapped_pairwise f _ _ row hp
    intro a ha b hb hne heq
    apply hne
    rw [(hcal a ha).2.1,(hcal b hb).2.1,heq]
  have hx' : max 4 (2*((row.map f).map (fun entry => entry.1.natAbs)).sum+p.natAbs+q.natAbs)≤x := by
    simpa only [signedCollectedRowBound,List.map_map,Function.comp_def,f] using hx
  have h := sparseSignedNumericalNonzero (row.map f) p q x hn' hv' hp' hx'
  simpa only [actualSignedCollectedValue,List.map_map,Function.comp_def,f] using h

end LogicLineages.OrdinalComparison
