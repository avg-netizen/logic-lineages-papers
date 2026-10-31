module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneOddTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneResponseProof
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

private theorem response_from_extension {G H : Type} [AddCommGroup G] [AddCommGroup H]
    {B D : AddSubgroup G} {C : AddSubgroup H} (f : B ≃+ C) (hBD : B ≤ D)
    (F : D →+ H) (hF : Function.Injective F)
    (hFa : ∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) (α : Ordinal)
    (hr : SubgroupComparison (AddMonoidHom.ofInjective hF).symm α)
    (n : ℕ) (b : Fin n → B) (m : ℕ) (d : Fin m → G) (hd : ∀ i, d i ∈ D) :
    ∃ c : Fin m → H, BackAndForth α (append (fun i => (b i:G)) d)
      (append (fun i => (f (b i):H)) c) := by
  let e := AddMonoidHom.ofInjective hF
  let s : Fin (n+m) → D := append (fun i => ⟨b i,hBD (b i).property⟩) (fun i => ⟨d i,hd i⟩)
  let t : Fin (n+m) → F.range := fun i => e (s i)
  let c : Fin m → H := fun i => F ⟨d i,hd i⟩
  have hleft : (fun i => (e.symm (t i):G)) = append (fun i => (b i:G)) d := by
    funext i
    dsimp only [t]
    rw [AddEquiv.symm_apply_apply]
    induction i using Fin.addCases <;> simp [s,append]
  have hright : (fun i => (t i:H)) = append (fun i => (f (b i):H)) c := by
    funext i
    change F (s i) = _
    induction i using Fin.addCases <;> simp [s,c,append,hFa]
  have h := hr (n+m) t
  change BackAndForth α (fun i => (e.symm (t i):G)) (fun i => (t i:H)) at h
  rw [hleft,hright] at h
  exact ⟨c,h⟩

theorem terminal_one_odd_comparison : Targets.terminalOneOddComparison := by
  classical
  intro G H _ _ _ _ p _ hG hH rG rH B C _ f γ lG lH hRank hpres n b a hb henum hab hbf
  intro k z
  apply (back_forth_successor (2*γ) H G k (fun i => (f (z i):H)) (fun i => (z i:G))).mpr
  intro m d
  let D : AddSubgroup G := B ⊔ AddSubgroup.closure (Set.range d)
  letI : Finite D := p_primary_finite_tuple_extension G p (Fact.out : p.Prime).ne_zero hG B m d
  have hBD : B ≤ D := le_sup_left
  have hd (i) : d i ∈ D :=
    (le_sup_right : AddSubgroup.closure (Set.range d) ≤ D) (AddSubgroup.subset_closure ⟨i,rfl⟩)
  let δ : Ordinal := Ordinal.omega0*γ
  have hδ : δ=0 ∨ Order.IsSuccLimit δ := by
    by_cases hz : γ=0
    · left; simp [δ,hz]
    · right; exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
        (lt_of_le_of_ne zero_le (Ne.symm hz))
  obtain ⟨F,hF,hFa,hFp⟩ := terminal_one_response G H p hG hH D B C f δ hδ hBD hpres
    (fun α hα => (hRank α hα).le) n b a hb henum hab hbf
  let e : D ≃+ F.range := AddMonoidHom.ofInjective hF
  letI : Finite F.range := Finite.of_surjective e e.surjective
  have hp : MapCutsExact p e.symm δ := by
    intro c β hβ
    have hv : F (e.symm c) = (c:H) := congrArg Subtype.val (e.apply_symm_apply c)
    have hh := hFp (e.symm c) β hβ
    rw [hv] at hh
    exact hh.symm
  have hr := reduced_limit_cut_comparison H G p hH hG rH rG F.range D e.symm γ lH lG
    (fun α hα => (hRank α hα).symm) hp
  exact response_from_extension f hBD F hF hFa (2*γ) hr k z m d hd
end LogicLineages.ModelsAlgebra.PGroups
