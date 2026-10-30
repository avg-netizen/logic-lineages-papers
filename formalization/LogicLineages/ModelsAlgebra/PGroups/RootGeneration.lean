module
public import LogicLineages.ModelsAlgebra.PGroups.RootGenerationTargets
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocle
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open scoped BigOperators

private theorem socle_smul_coe (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (c : ZMod p) (z : pSocle p (⊤ : AddSubgroup G)) :
    ((c • z : pSocle p (⊤ : AddSubgroup G)) : G) = c.val • (z : G) := by
  have h : c • z = c.val • z := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  exact congrArg (fun w : pSocle p (⊤ : AddSubgroup G) => (w : G)) h

theorem ulm_roots_generate : Targets.groupUlmRootsGenerate := by
  classical
  intro p _ G _ N hbound I b x y hx hy
  let C := AddSubgroup.closure (Set.range (fun a : Σ l : Fin N, I l => y a.1 a.2))
  have hgen : ∀ n : ℕ, n ≤ N → ∀ z : G, p ^ n • z = 0 → z ∈ C := by
    intro n
    induction n with
    | zero =>
      intro hn z hz
      have hz0 : z = 0 := by simpa using hz
      rw [hz0]
      exact C.zero_mem
    | succ m ih =>
      intro hm z hz
      let w : pSocle p (⊤ : AddSubgroup G) := ⟨p ^ m • z, ⟨AddSubgroup.mem_top _, by
        change p • (p ^ m • z) = 0
        simpa only [pow_succ', mul_smul] using hz⟩⟩
      have hw : w ∈ socleLevel p G m := by
        exact (finite_filtration_multiple_image G p m).ge ⟨z,rfl⟩
      rw [adapted_socle_filtered_span p G N hbound I b x hx m (by omega)] at hw
      obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
      let t : G := c.sum (fun a r => r.val • (p ^ (a.val.1.val - m) • y a.val.1 a.val.2))
      have ht : t ∈ C := by
        dsimp only [t, Finsupp.sum]
        apply C.sum_mem
        intro a ha
        exact C.nsmul_mem (C.nsmul_mem (AddSubgroup.subset_closure ⟨a.val,rfl⟩) _) _
      have hc' : c.sum (fun a r => r.val • (x a.val.1 a.val.2 : G)) = p ^ m • z := by
        calc
          _ = (pSocle p (⊤ : AddSubgroup G)).subtype
              (c.sum (fun a r => r • includedSocleFamily p N I x a.val)) := by
            rw [map_finsuppSum]
            unfold Finsupp.sum
            apply Finset.sum_congr rfl
            intro a ha
            exact (socle_smul_coe p G (c a) (includedSocleFamily p N I x a.val)).symm
          _ = _ := congrArg (pSocle p (⊤ : AddSubgroup G)).subtype hc
      have hpower : p ^ m • t = p ^ m • z := by
        change (nsmulAddMonoidHom (p ^ m)) (c.sum (fun a r => r.val •
          (p ^ (a.val.1.val - m) • y a.val.1 a.val.2))) = _
        rw [map_finsuppSum]
        calc
          _ = c.sum (fun a r => r.val • (x a.val.1 a.val.2 : G)) := by
            unfold Finsupp.sum
            apply Finset.sum_congr rfl
            intro a ha
            have hp : p ^ m • (p ^ (a.val.1.val - m) • y a.val.1 a.val.2) =
                (x a.val.1 a.val.2 : G) := by
              rw [← mul_smul, ← pow_add, Nat.add_sub_of_le a.property, hy]
            change p ^ m • ((c a).val • (p ^ (a.val.1.val - m) • y a.val.1 a.val.2)) = _
            rw [smul_comm (p ^ m) (c a).val, hp]
          _ = _ := hc'
      have hdiff : p ^ m • (z - t) = 0 := by rw [smul_sub, hpower, sub_self]
      have hadd := C.add_mem (ih (by omega) (z-t) hdiff) ht
      simpa only [sub_add_cancel] using hadd
  apply le_antisymm le_top
  intro z hz
  exact hgen N le_rfl z (hbound z)

theorem bounded_socle_detects_injectivity : Targets.groupBoundedSocleDetectsInjectivity := by
  intro p N A B _ _ f hbound hs
  apply (injective_iff_map_eq_zero f).mpr
  intro a ha
  have h : ∀ n : ℕ, ∀ a : A, p ^ n • a = 0 → f a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a hz ha; simpa using hz
    | succ n ih =>
      intro a hz ha
      apply hs a
      · apply ih (p • a)
        · simpa only [← mul_smul, ← pow_succ] using hz
        · rw [map_nsmul, ha, smul_zero]
      · exact ha
  exact h N a (hbound a) ha
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
