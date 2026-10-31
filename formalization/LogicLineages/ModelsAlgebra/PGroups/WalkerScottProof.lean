module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGammaProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailScottProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailLowerProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedOddSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLower
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailProof
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailLowerProof
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteTerminalSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
private theorem nontrivial_of_length (p:ℕ) (G:Type) [AddCommGroup G] (ell:Ordinal.{0})
    (he:0<ell) (hl:PGroupExactLength p G ell) : Nontrivial G := by
  obtain ⟨x,hx⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp (hl.2 0 he)
  exact ⟨⟨(x:G),0,fun h=>hx (Subtype.ext h)⟩⟩
private theorem tail_rank (p:ℕ) (G:Type) [AddCommGroup G] (δ:Ordinal.{0}) (j:ℕ) :
    TerminalRank p (transfiniteFiltration p δ:AddSubgroup G) j =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (δ+j):AddSubgroup G)) := by
  have h := transfinite_tail_ulm_rank G p δ (j:Ordinal)
  rw [finite_ordinal_filtration] at h
  exact h

private theorem even_tail_zero (p:ℕ) [Fact p.Prime] (γ:Ordinal.{0}) [Countable γ.ToType] (r:ℕ) :
    TerminalRank p (transfiniteFiltration p (walkerGammaCut γ):AddSubgroup (WalkerEven p (walkerGammaCut γ) r)) 0=(r:Cardinal) := by
  let δ := walkerGammaCut γ
  let E := WalkerEven p δ r
  letI : Countable δ.ToType := walker_countable_gamma_cut γ
  have ht := walker_family_ulm_table p δ r
  have htab := (ht δ).2
  rw [if_neg (lt_irrefl δ),if_pos rfl] at htab
  have hidx : δ+(0:ℕ)=δ := by simp
  have hcast := congrArg (fun α:Ordinal.{0}=>Module.rank (ZMod p)
    (UlmLayer p (transfiniteFiltration p α:AddSubgroup E))) hidx
  exact (tail_rank p E δ 0).trans (hcast.trans htab)

private theorem even_tail_one (p:ℕ) [Fact p.Prime] (γ:Ordinal.{0}) [Countable γ.ToType] (r:ℕ) :
    TerminalRank p (transfiniteFiltration p (walkerGammaCut γ):AddSubgroup (WalkerEven p (walkerGammaCut γ) r)) 1=Cardinal.aleph0 := by
  let δ := walkerGammaCut γ
  let E := WalkerEven p δ r
  letI : Countable δ.ToType := walker_countable_gamma_cut γ
  have ht := walker_family_ulm_table p δ r
  have htab := (ht (δ+1)).2
  have hlt : ¬δ+1<δ := not_lt_of_ge le_self_add
  have hne : δ+1≠δ := (Order.lt_succ δ).ne'
  rw [if_neg hlt,if_neg hne,if_pos rfl] at htab
  have hidx : δ+(1:ℕ)=δ+1 := by simp
  have hcast := congrArg (fun α:Ordinal.{0}=>Module.rank (ZMod p)
    (UlmLayer p (transfiniteFiltration p α:AddSubgroup E))) hidx
  exact (tail_rank p E δ 1).trans (hcast.trans htab)

theorem walker_scott_endpoints : Targets.walkerScottEndpoints := by
  classical
  intro p _ γ _ r hr
  let δ := walkerGammaCut γ
  let O := WalkerOdd p δ r
  let E := WalkerEven p δ r
  obtain ⟨ho,he,lo,le,⟨eo⟩,⟨ee⟩,ht,hi,_⟩ := walker_gamma_source_construction p γ r hr
  letI : Countable O := ho.1
  letI : Countable E := he.1
  have lo' : PGroupExactLength p O (Ordinal.omega0*γ+1) := lo
  have le' : PGroupExactLength p E (Ordinal.omega0*γ+2) := le
  letI : Nontrivial O := nontrivial_of_length p O _ (by positivity) lo'
  letI : Nontrivial E := nontrivial_of_length p E _ (by positivity) le'
  let HO := (transfiniteFiltration p δ:AddSubgroup O)
  let HE := (transfiniteFiltration p δ:AddSubgroup E)
  have hfin : Finite HO := Finite.of_injective eo eo.injective
  have hzero : TerminalRank p HE 0=(r:Cardinal) := even_tail_zero p γ r
  have hone : TerminalRank p HE 1=Cardinal.aleph0 := even_tail_one p γ r
  have hpattern : OneInfiniteTerminal p HE 2 2 := by
    refine ⟨by decide,le_rfl,?_,?_⟩
    · simpa only [Nat.reduceSub] using hone
    · intro j hj hne
      have hj0 : j=0 := by omega
      subst j
      rw [hzero]
      exact Cardinal.natCast_lt_aleph0
  have hshort : ∃j:ℕ,j<2-1 ∧ TerminalRank p HE j≠0 := by
    refine ⟨0,by decide,?_⟩
    rw [hzero]
    exact_mod_cast Nat.ne_of_gt hr
  have hinf : Infinite E := by
    letI := infinite_ulm_infinite_filtration p HE 1 hone
    letI : Infinite HE := Infinite.of_injective (fun x:(finiteFiltration p 1:AddSubgroup HE)=>(x:HE)) Subtype.val_injective
    exact Infinite.of_injective (fun x:HE=>(x:E)) Subtype.val_injective
  have hbound := (exact_length_terminal_bound E p γ 2 (by simpa only [Nat.cast_ofNat] using le')).1
  have hEven : RawDifferenceEndpoint E (2*γ+2) := by
    have hinfTail : Infinite HE := by
      letI := infinite_ulm_infinite_filtration p HE 1 hone
      exact Infinite.of_injective (fun x:(finiteFiltration p 1:AddSubgroup HE)=>(x:HE)) Subtype.val_injective
    exact ⟨one_infinite_tail_difference_upper p E γ 2 2 he.2.1 (by decide) le_rfl hbound hpattern.2.2.1 hpattern.2.2.2,
      infinite_terminal_no_raw_sigma E p he.2.1 he.2.2 γ 2 hbound hinfTail,
      one_infinite_tail_no_pi p E γ 2 2 he.2.1 he.2.2 (by decide) le_rfl hbound hpattern.2.2.1 hpattern.2.2.2 hshort⟩
  have hOdd : RawDifferenceEndpoint O (2*γ+1) := by
    letI : Finite HO := hfin
    refine ⟨finite_tail_scott_upper p O γ ho.2.1 hfin,?_,?_⟩
    · by_cases hz:γ=0
      · subst γ
        letI : Finite O := Finite.of_injective (fun x:O=>(⟨x,by simp [HO,δ,walkerGammaCut,transfiniteFiltration_zero]⟩:HO))
          (by intro x y h; exact congrArg Subtype.val h)
        simpa only [mul_zero,zero_add] using raw_finite_no_sigma_one_scott O
      · exact reduced_odd_no_raw_sigma O p ho.2.1 ho.2.2 γ (lt_of_le_of_ne zero_le (Ne.symm hz))
          (fun α hα=>lo'.2 α (hα.trans_le le_self_add))
    · by_cases hz:γ=0
      · subst γ
        simpa only [mul_zero,zero_add] using raw_nontrivial_no_pi_one_scott O
      · apply finite_tail_no_pi O p ho.2.1 ho.2.2 γ (lt_of_le_of_ne zero_le (Ne.symm hz)) hfin
        exact lo'.2 _ (Order.lt_succ _)
  exact ⟨hOdd,hEven,hinf,fun hγ=>(hi hγ).1⟩
end LogicLineages.ModelsAlgebra.PGroups
