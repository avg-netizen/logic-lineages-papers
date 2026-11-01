module
public import LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaTargets
public import LogicLineages.ModelsAlgebra.PGroups.OddObstructionCompleteProof
public import LogicLineages.ModelsAlgebra.PGroups.ShortStableScottProof
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteSocleOddProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedReducedProductProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleTailCollapseProof
public import LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottProof
public import LogicLineages.ModelsAlgebra.PGroups.LimitSigmaScottProof
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorParityProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

private theorem raw_sigma_scott_pullback (G H:Type) [AddCommGroup G] [AddCommGroup H]
    [Countable H] (e:G≃+H) (α:Ordinal.{0}) (φ:Formula 0)
    (hc:Complexity .sigma α φ) (hs:RawScottSentence (RawGroupStructure.ofGroup H) φ) :
    RawScottSentence (RawGroupStructure.ofGroup G) φ := by
  have hbf:=comparison_isomorphism α G H e 0 Fin.elim0
  have hnil:(fun i:Fin 0=>e (Fin.elim0 i))=(Fin.elim0:Fin 0→H):=funext (fun i=>i.elim0)
  rw [hnil] at hbf
  refine ⟨(raw_formula_agreement G 0 Fin.elim0 φ).mpr
    ((truth_transfer α G H 0 Fin.elim0 Fin.elim0 hbf).2 φ hc
      ((raw_formula_agreement H 0 Fin.elim0 φ).mp hs.1)),?_⟩
  intro K _ S hK
  obtain ⟨u⟩:=hs.2 K S hK
  refine ⟨⟨e.toEquiv.trans u.toEquiv,?_,?_,?_⟩⟩
  · change u.toEquiv (e 0)=S.zero
    rw [e.map_zero]
    exact u.map_zero
  · intro x
    change u.toEquiv (e (-x))=S.neg (u.toEquiv (e x))
    rw [map_neg]
    exact u.map_neg (e x)
  · intro x y
    change u.toEquiv (e (x+y))=S.add (u.toEquiv (e x)) (u.toEquiv (e y))
    rw [map_add]
    exact u.map_add (e x) (e y)

theorem primary_even_sigma_lowering : Targets.primaryEvenSigmaLowering := by
  classical
  intro p _ G _ _ γ _ hG hγ φ hφ hScott
  obtain ⟨_,R,_,_,hred,_,_,e,_⟩:=actual_divisible_splitting G
  let D:AddSubgroup G:=divisiblePart G
  have hR:∀x:R,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩:=hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hD:∀x:D,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩:=hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hd:GroupDivisible D:=(actual_divisible_part G).1
  obtain ⟨ell,hell,_⟩:=countable_reduced_exact_length R p hR hred
  have hmem:=(divisible_product_data R D p hR hD hd).2.1
  have hmap (β:Ordinal.{0}):(transfiniteFiltration p β:AddSubgroup (R×D)).map e.toAddMonoidHom=
      (transfiniteFiltration p β:AddSubgroup G) := by
    have hk:e.toAddMonoidHom.ker≤(transfiniteFiltration p β:AddSubgroup (R×D)) := by
      rw [e.toAddMonoidHom.ker_eq_bot e.injective]
      exact bot_le
    exact map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective β hk β le_rfl
  let δ:=Ordinal.omega0*γ
  by_cases hshort:ell<δ
  · have hznext:(transfiniteFiltration p (ell+1):AddSubgroup R)=⊥ :=
      le_antisymm ((transfiniteFiltration_antitone p le_self_add).trans hell.2.1.le) bot_le
    have hsP:(transfiniteFiltration p ell:AddSubgroup (R×D))=transfiniteFiltration p (ell+1) := by
      ext x
      rw [hmem ell x,hmem (ell+1) x,hell.2.1,hznext]
    have hsG:StableAt p G ell := by
      change (transfiniteFiltration p ell:AddSubgroup G)=transfiniteFiltration p (ell+1)
      rw [←hmap ell,←hmap (ell+1),hsP]
    exact Or.inl (short_stable_scott_upper p G γ ell hell.1 hG hshort hsG)
  have hlong:StagesNonzeroBelow p R δ:=fun ξ hξ=>hell.2.2 ξ (hξ.trans_le (le_of_not_gt hshort))
  have hsP:=raw_sigma_scott_pullback (R×D) G e (2*γ+2) φ hφ hScott
  by_cases hvery:δ+Ordinal.omega0≤ell
  · have hγpos:0<γ+1 :=lt_of_le_of_lt zero_le (Order.lt_succ γ)
    have hc:Complexity .sigma (2*(γ+1)+1) φ :=
      GroupInfinitary.positive_complexity_monotone .sigma (2*γ+2) (2*(γ+1)+1) 0 φ
        (by positivity) (by rw [mul_add_one]; exact le_self_add) hφ
    have hlong':StagesNonzeroBelow p R (Ordinal.omega0*(γ+1)):=by
      intro ξ hξ
      apply hell.2.2 ξ
      exact hξ.trans_le (by simpa only [mul_add_one] using hvery)
    exact (divisible_product_odd_no_raw_sigma R D p hR hD hred hd (γ+1) hγpos hlong' φ hc hsP).elim
  rcases finite_or_infinite (pSocle p (⊤:AddSubgroup D)) with hDfin|hDinf
  · letI:=hDfin
    have hbelow:ell<δ+Ordinal.omega0:=lt_of_not_ge hvery
    obtain ⟨ξ,hξ,hbound⟩:=Ordinal.lt_add_iff Ordinal.omega0_ne_zero |>.mp hbelow
    obtain ⟨N,rfl⟩:=Ordinal.lt_omega0.mp hξ
    have hz:(transfiniteFiltration p (δ+N):AddSubgroup R)=⊥ :=
      le_antisymm ((transfiniteFiltration_antitone p hbound).trans hell.2.1.le) bot_le
    have hkill:∀x:(transfiniteFiltration p δ:AddSubgroup R),p^N • x=0 := by
      intro x
      have hx:p^N • x∈(transfiniteFiltration p (N:Ordinal.{0}):AddSubgroup (transfiniteFiltration p δ:AddSubgroup R)) := by
        rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
        exact ⟨x,rfl⟩
      have hm:=(transfinite_tail_membership R p δ (N:Ordinal.{0}) (p^N • x)).mp hx
      rw [hz,AddSubgroup.mem_bot] at hm
      exact Subtype.ext hm
    rcases finite_or_infinite (transfiniteFiltration p δ:AddSubgroup R) with hRfin|hRinf
    · letI:=hRfin
      letI:Finite (pSocle p (transfiniteFiltration p δ:AddSubgroup (R×D))):=
        product_cut_socle_finite R D p hR hD hd δ
      let i:=filtrationSocleEquiv p e δ
      letI:Finite (pSocle p (transfiniteFiltration p δ:AddSubgroup G)):=Finite.of_equiv _ i.toEquiv
      let T:AddSubgroup G:=transfiniteFiltration p δ
      let j:pSocle p (⊤:AddSubgroup T)→pSocle p T:=fun x=>
        ⟨((x:T):G),(x:T).property,congrArg Subtype.val x.property.2⟩
      have hj:Function.Injective j:=by
        intro x y h
        exact Subtype.ext (Subtype.ext (congrArg (fun z:pSocle p T=>(z:G)) h))
      have hT:Finite (pSocle p (⊤:AddSubgroup T)):=Finite.of_injective j hj
      exact Or.inr (finite_socle_tail_raw_sigma_lowering p G γ hγ hG hT φ hφ hScott)
    · exact (bounded_reduced_product_no_even_raw_sigma R D p hR hD hred hd γ N hkill hRinf φ hφ hsP).elim
  · letI:=hDinf
    exact (infinite_socle_no_even_raw_sigma R D p hR hD hred hd γ inferInstance hlong φ hφ hsP).elim

theorem primary_all_sigma_lowering : Targets.primaryAllSigmaLowering := by
  classical
  intro p _ G _ _ α _ hG φ hφ hScott
  rcases Ordinal.zero_or_succ_or_isSuccLimit α with hz|⟨β,hβ⟩|hlimit
  · subst α
    exact (primary_no_raw_sigma_zero p G hG φ hφ hScott).elim
  · subst α
    have hcount:Countable (β+1).ToType := by simpa only [Order.succ_eq_add_one] using (inferInstance:Countable (Order.succ β).ToType)
    obtain ⟨γ,hγ,hform⟩:=countable_successor_parity β hcount
    letI:=hγ
    rcases hform with hodd|heven
    · have hα:Order.succ β=2*γ+1:=by simpa only [Order.succ_eq_add_one] using hodd
      rw [hα] at hφ
      by_cases hz:γ=0
      · subst γ
        simp only [mul_zero,zero_add] at hφ
        exact (primary_no_raw_sigma_one p G hG φ hφ hScott).elim
      · have hp:0<γ:=lt_of_le_of_ne zero_le (Ne.symm hz)
        obtain ⟨d,hd,hs⟩:=odd_primary_sigma_lowering p G γ hG hp φ hφ hScott
        refine ⟨2*γ,?_,Or.inr (Or.inr ⟨d,hd,hs⟩)⟩
        rw [hα]
        exact Order.lt_succ _
    · have hα:Order.succ β=2*γ+2:=by simpa only [Order.succ_eq_add_one] using heven
      rw [hα] at hφ
      by_cases hz:γ=0
      · subst γ
        simp only [mul_zero,zero_add] at hφ
        obtain ⟨_,d,hd,hs⟩:=primary_raw_sigma_two_lowering p G hG φ hφ hScott
        refine ⟨1,?_,Or.inr (Or.inr ⟨d,hd,hs⟩)⟩
        rw [hα]
        simp
      · have hp:0<γ:=lt_of_le_of_ne zero_le (Ne.symm hz)
        have hres:=primary_even_sigma_lowering p G γ hG hp φ hφ hScott
        refine ⟨2*γ+1,?_,Or.inr hres⟩
        rw [hα]
        exact (add_lt_add_iff_left (2*γ)).mpr one_lt_two
  · obtain ⟨β,hβα,ψ,hψ,hsψ⟩:=raw_limit_sigma_scott_lowering G (RawGroupStructure.ofGroup G) α hlimit φ hφ hScott
    exact ⟨β,hβα,Or.inl ⟨ψ,hψ,hsψ⟩⟩
end LogicLineages.ModelsAlgebra.PGroups
