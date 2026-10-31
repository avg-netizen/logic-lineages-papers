module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedDifferenceIndexTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReducedScottCompleteProof
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyProof
public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLower
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
private theorem lift_difference (G:Type) [AddCommGroup G] (α β:Ordinal.{0}) (hab:α<β)
    (d:DifferenceFormula 0) (hd:d.AtLevel α) (hs:RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d) :
    ∃φ:Formula 0, Complexity .pi β φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ := by
  have h := raw_difference_pi_lift α β hab 0 d hd
  refine ⟨differencePiLift d,h.1,(h.2 G _ Fin.elim0).mpr hs.1,?_⟩
  intro H _ R ht
  exact hs.2 H R ((h.2 H R Fin.elim0).mp ht)
private theorem lift_pi_sigma (G:Type) [AddCommGroup G] (α β:Ordinal.{0}) (hab:α<β)
    (φ:Formula 0) (hc:Complexity .pi α φ) (hs:RawScottSentence (RawGroupStructure.ofGroup G) φ) :
    ∃ψ:Formula 0, Complexity .sigma β ψ ∧ RawScottSentence (RawGroupStructure.ofGroup G) ψ := by
  refine ⟨sigmaWrap φ,sigma_wrap_complexity β α (ne_of_gt (lt_of_le_of_lt zero_le hab)) hab 0 φ hc,
    ((raw_wrapper_truth 0 φ G _ Fin.elim0).2).mpr hs.1,?_⟩
  intro H _ R ht
  exact hs.2 H R (((raw_wrapper_truth 0 φ H R Fin.elim0).2).mp ht)
private theorem difference_distinct (G:Type) [AddCommGroup G] (α β:Ordinal.{0})
    (ha:RawDifferenceEndpoint G α) (hb:RawDifferenceEndpoint G β) (hne:α≠β) : False := by
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · obtain ⟨d,hd,hs⟩ := ha.1
    obtain ⟨φ,hφ,hS⟩ := lift_difference G α β hlt d hd hs
    exact hb.2.2 φ hφ hS
  · obtain ⟨d,hd,hs⟩ := hb.1
    obtain ⟨φ,hφ,hS⟩ := lift_difference G β α hgt d hd hs
    exact ha.2.2 φ hφ hS
private theorem pi_below (G:Type) [AddCommGroup G] (α β:Ordinal.{0}) (hb:β≠0) (hle:β≤α)
    (ha:RawDifferenceEndpoint G α) (hp:RawPiEndpoint G β) : False := by
  obtain ⟨φ,hφ,hs⟩ := hp.1
  exact ha.2.2 φ (positive_complexity_monotone .pi β α hb hle 0 φ hφ) hs
private theorem pi_step (G:Type) [AddCommGroup G] (α θ:Ordinal.{0}) (hα:Order.IsSuccLimit α)
    (ha:RawDifferenceEndpoint G α) (hp:RawPiEndpoint G (θ+1)) (hd:NoRawDifference G θ) : False := by
  by_cases hle:θ+1≤α
  · exact pi_below G α (θ+1) (ne_of_gt (by positivity)) hle ha hp
  · have hlt:α<θ+1 := lt_of_not_ge hle
    have hαθ:α≤θ := Order.le_of_lt_succ (by simpa only [Order.succ_eq_add_one] using hlt)
    obtain ⟨d,hD,hS⟩ := ha.1
    exact hd d ⟨positive_complexity_monotone .sigma α θ hα.ne_zero hαθ 0 _ hD.1,
      positive_complexity_monotone .pi α θ hα.ne_zero hαθ 0 _ hD.2⟩ hS
private theorem pi_double (G:Type) [AddCommGroup G] (α θ:Ordinal.{0}) (hα:Order.IsSuccLimit α)
    (ha:RawDifferenceEndpoint G α) (hp:RawPiEndpoint G (θ+2)) : False := by
  by_cases hle:θ+2≤α
  · exact pi_below G α (θ+2) (ne_of_gt (by positivity)) hle ha hp
  · have hlt:α<(θ+1)+1 := by simpa only [add_assoc,one_add_one_eq_two] using lt_of_not_ge hle
    have hmid : α≤Order.succ θ := Order.le_of_lt_succ hlt
    have hlow : α≤θ := hα.le_succ_iff.mp hmid
    have hnext : α+1<θ+2 := by
      have hh := (Order.succ_le_succ hlow).trans_lt (Order.lt_succ (Order.succ θ))
      simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using hh
    obtain ⟨d,hd,hs⟩ := ha.1
    obtain ⟨φ,hφ,hS⟩ := lift_difference G α (α+1) (Order.lt_succ α) d hd hs
    obtain ⟨ψ,hψ,hT⟩ := lift_pi_sigma G (α+1) (θ+2) hnext φ hφ hS
    exact hp.2 ψ hψ hT

theorem reduced_no_limit_difference_index : Targets.reducedNoLimitDifferenceIndex := by
  classical
  intro G _ _ p _ hG hr α hα ha
  rcases subsingleton_or_nontrivial G with hs|hn
  · letI := hs
    obtain ⟨φ,hφ,hS⟩ := (raw_trivial_exact G).1
    have hle : (1:Ordinal.{0})≤α := Order.one_le_iff_ne_zero.mpr hα.ne_zero
    exact ha.2.2 φ (positive_complexity_monotone .pi 1 α one_ne_zero hle 0 φ hφ) hS
  · letI := hn
    have hc := reduced_scott_full_source.1 G p hG hr
    obtain ⟨⟨γ,N⟩,hz,_⟩ := hc.1
    letI : Countable γ.ToType := hz.1
    have hrows := hc.2 γ N hz.2
    by_cases hN:N=0
    · have h := hrows.1 hN
      exact pi_step G α (2*γ) hα ha h.2.1 h.2.2
    · have h := hrows.2 (Nat.pos_of_ne_zero hN)
      rcases h.2.1 with hfin|hone|htwo
      · exact difference_distinct G α (2*γ+1) ha (h.2.2.1 hfin)
          (Ne.symm (by simpa only [Order.succ_eq_add_one] using hα.succ_ne (2*γ)))
      · obtain ⟨k,hk⟩ := hone
        have hkrows := h.2.2.2.1 k hk
        by_cases hs:∀j:ℕ,j<k-1 → TerminalRank p (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G) j=0
        · exact pi_double G α (2*γ) hα ha (hkrows.1 hs)
        · push_neg at hs
          exact difference_distinct G α (2*γ+2) ha (hkrows.2 hs)
            (Ne.symm (by simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using hα.succ_ne (2*γ+1)))
      · have hh := h.2.2.2.2 htwo
        apply pi_step G α (2*γ+2) hα ha _ hh.2
        simpa only [add_assoc,show (2:Ordinal.{0})+1=3 from by norm_num] using hh.1

theorem raw_no_zero_difference_scott : Targets.rawNoZeroDifferenceScott := by
  classical
  intro G _ _ d hd hs
  rcases subsingleton_or_nontrivial G with hsub|hnt
  · letI := hsub
    have hσ := hd.1
    have hπ := hd.2
    obtain ⟨q,hq⟩ : ∃q:QF 0,d.sigmaPart=Formula.qf q := by
      generalize he:d.sigmaPart=φ at hσ
      cases hσ with
      | qf _ q => exact ⟨q,rfl⟩
      | sigma hpos _ _ _ _ _ _ => exact (hpos rfl).elim
    obtain ⟨r,hr⟩ : ∃r:QF 0,d.piPart=Formula.qf r := by
      generalize he:d.piPart=φ at hπ
      cases hπ with
      | qf _ r => exact ⟨r,rfl⟩
      | pi hpos _ _ _ _ _ _ => exact (hpos rfl).elim
    apply (raw_trivial_exact G).2 (QF.and q r)
    have hsem (H:Type) (R:RawGroupStructure H) :
        d.RawRealize R Fin.elim0 ↔ (Formula.qf (QF.and q r)).RawRealize R Fin.elim0 := by
      change (d.sigmaPart.RawRealize R Fin.elim0 ∧ d.piPart.RawRealize R Fin.elim0) ↔ _
      rw [hq,hr]
      rfl
    refine ⟨(hsem G _).mp hs.1,?_⟩
    intro H _ R ht
    exact hs.2 H R ((hsem H R).mpr ht)
  · letI := hnt
    obtain ⟨φ,hφ,hS⟩ := lift_difference G 0 1 zero_lt_one d hd hs
    exact raw_nontrivial_no_pi_one_scott G φ hφ hS
end LogicLineages.ModelsAlgebra.PGroups
