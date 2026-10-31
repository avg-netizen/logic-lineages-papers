module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTerminalDeletionTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedFiniteSummandProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionOddProof
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

theorem finite_terminal_deletion : Targets.finiteTerminalDeletion := by
  classical
  intro G _ _ p _ hG rG γ N hN hinf n a
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  letI : Infinite S := hinf
  have hex : ∃ k : ℕ, ∀ x : S, p^k • x=0 := ⟨N,hN⟩
  let k := Nat.find hex
  have hk : ∀ x : S, p^k • x=0 := Nat.find_spec hex
  have hpos : 0<k := by
    apply Nat.pos_of_ne_zero
    intro hzero
    obtain ⟨x,hx⟩ := exists_ne (0:S)
    exact hx (by simpa only [hzero,pow_zero,one_nsmul] using hk x)
  obtain ⟨x,hx⟩ := not_forall.mp (Nat.find_min hex (Nat.sub_lt hpos (by decide : 0<1)))
  let A : AddSubgroup G := AddSubgroup.closure (Set.range a)
  letI : Finite A := p_primary_finite_tuple_closure G p (Fact.out : p.Prime).ne_zero hG n a
  let B : AddSubgroup S := A.comap S.subtype
  let j : B → A := fun b => ⟨b.val.val,b.property⟩
  letI : Finite B := Finite.of_injective j (by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z:G)) h)
  obtain ⟨K0,T0,hfin,hBK,hxK,hd,hs⟩ := bounded_finite_summand p S k hk B x
  letI : Finite K0 := hfin
  let K : AddSubgroup G := K0.map S.subtype
  let T : AddSubgroup G := T0.map S.subtype
  letI : Finite K := Finite.of_equiv K0 (AddSubgroup.equivMapOfInjective K0 S.subtype Subtype.val_injective).toEquiv
  have hsplit : S=K ⊔ T := by
    change S=K0.map S.subtype ⊔ T0.map S.subtype
    rw [← AddSubgroup.map_sup,hs,← AddMonoidHom.range_eq_map,AddSubgroup.range_subtype]
  have hdis : Disjoint K T := AddSubgroup.disjoint_map Subtype.val_injective hd
  have horder : ∃ y : K, p^(k-1) • y ≠ 0 := by
    refine ⟨⟨x,⟨x,hxK,rfl⟩⟩,?_⟩
    intro h
    apply hx
    apply Subtype.ext
    exact congrArg (fun z : K => (z:G)) h
  have hh := terminal_deletion_odd G p hG rG γ K T k hsplit hdis hpos hk horder
  obtain ⟨et⟩ := hh.2.1
  letI : Finite (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) := Finite.of_equiv K et.symm.toEquiv
  have hret : A ⊓ S ≤ K := by
    intro y hy
    exact ⟨⟨y,hy.2⟩,hBK hy.1,rfl⟩
  refine ⟨T,(T0.map_le_range S.subtype).trans_eq S.range_subtype,inferInstance,?_,hh.2.2.2.2.2 n a hret⟩
  rintro ⟨e⟩
  have hker : e.toAddMonoidHom.ker ≤ S := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective δ hker δ le_rfl
  let f : S → (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) :=
    fun x => ⟨e x,hm.le ⟨x,x.property,rfl⟩⟩
  have hfi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) => (z:G ⧸ T)) h
  exact (not_finite_iff_infinite.mpr hinf) (Finite.of_injective f hfi)
end LogicLineages.ModelsAlgebra.PGroups
