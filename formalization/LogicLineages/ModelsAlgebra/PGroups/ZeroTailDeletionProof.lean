module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroTailDeletionTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneOddProof
public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientFiltration
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotient
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

theorem zero_tail_deletion : Targets.zeroTailDeletion := by
  classical
  intro G _ _ p _ hG rG γ hγ lG N hbound
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  let Q := G ⧸ S
  let q := QuotientAddGroup.mk' S
  letI : Countable Q := (QuotientAddGroup.mk'_surjective S).countable
  have hQ := p_primary_quotient G p S hG
  have hδ : Order.IsSuccLimit δ := Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hγ
  have hquot := full_quotient_filtration p S γ le_rfl
  have hzero : (transfiniteFiltration p δ : AddSubgroup Q) = ⊥ := by
    rw [hquot.1 δ le_rfl]
    apply (AddSubgroup.map_eq_bot_iff S).mpr
    simp only [QuotientAddGroup.ker_mk',le_refl]
  have rQ : IsReducedAddGroup Q := zero_stage_reduced Q p (Fact.out : p.Prime).ne_zero δ hzero
  have hRank : UlmRanksAgreeBelow p G Q δ := fun α hα => (hquot.2 α hα).2
  have lQ : StagesNonzeroBelow p Q δ := by
    intro α hα hz
    have hle : (transfiniteFiltration p α : AddSubgroup G) ≤ S := by
      have hh := (AddSubgroup.map_eq_bot_iff (transfiniteFiltration p α : AddSubgroup G)).mp ((hquot.1 α hα.le).symm.trans hz)
      simpa only [QuotientAddGroup.ker_mk'] using hh
    let A : AddSubgroup G := transfiniteFiltration p α
    have hb : ∀ x : A, p^N • x=0 := by
      intro x
      exact Subtype.ext (congrArg (fun z : S => (z:G)) (hbound ⟨x,hle x.property⟩))
    have hA0 : (transfiniteFiltration p (N:Ordinal) : AddSubgroup A) = ⊥ := by
      rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image]
      apply le_antisymm
      · rintro x ⟨y,rfl⟩; exact hb y
      · exact bot_le
    have hG0 : (transfiniteFiltration p (α+(N:Ordinal)) : AddSubgroup G) = ⊥ := by
      rw [← transfinite_tail_image,hA0,AddSubgroup.map_bot]
    have hlt : ∀ k : ℕ, α+(k:Ordinal)<δ := by
      intro k
      induction k with
      | zero => simpa using hα
      | succ k ih => simpa only [Nat.cast_add,Nat.cast_one,add_assoc,Order.succ_eq_add_one] using hδ.succ_lt ih
    exact lG _ (hlt N) hG0
  refine ⟨inferInstance,hQ,rQ,hRank,hzero,lQ,?_,?_⟩
  · let U : AddSubgroup Q := transfiniteFiltration p δ
    letI : Subsingleton U := ⟨fun x y => Subtype.ext ((hzero.le x.property).trans (hzero.le y.property).symm)⟩
    let f : (⊥ : AddSubgroup Q) ≃+ (⊥ : AddSubgroup G) := AddEquiv.ofUnique
    have hp : MapCutsExact p f δ := by
      intro x β _
      have hx : (x:Q)=0 := x.property
      have hy : (f x:G)=0 := (f x).property
      simp only [hx,hy,AddSubgroup.zero_mem]
    let b : Fin 1 → U := fun _ => 0
    let a : Fin 1 → S := fun _ => 0
    have hbf : BackAndForth (1:Ordinal) a b := by
      have hs := back_forth_successor 0 S U 1 a b
      simp only [zero_add] at hs
      apply hs.mpr
      intro m d
      refine ⟨fun _ => 0,(zero_comparison U S (1+m) _ _).mpr ?_⟩
      have hi : Function.Injective (0:U →+ S) := fun _ _ _ => Subsingleton.elim _ _
      have he := embedding_atomic_agreement U S (0:U →+ S) hi (1+m) (append b d)
      have hv : (fun i => (0:U →+ S) (append b d i)) = append a (fun _ : Fin m => (0:S)) := by
        funext i
        induction i using Fin.addCases <;> simp [append,a]
      rw [hv] at he
      exact he
    have hodd := terminal_one_odd_comparison Q G p hQ hG rQ rG ⊥ ⊥ f γ lQ lG
      (fun α hα => (hRank α hα).symm) hp 1 b a (fun _ => by exact (⊥:AddSubgroup Q).zero_mem)
      (fun x hx _ => ⟨0,hx.symm⟩) (fun i => by
        change (0:G) = (f 0:G)
        rw [map_zero]; rfl) hbf
    convert hodd 0 (Fin.elim0 : Fin 0 → (⊥:AddSubgroup Q)) using 1 <;> funext i <;> exact Fin.elim0 i
  · intro hS he
    obtain ⟨e⟩ := he
    have hk : e.toAddMonoidHom.ker ≤ S := by
      rw [e.toAddMonoidHom.ker_eq_bot e.injective]; exact bot_le
    have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective δ hk δ le_rfl
    have hm0 : S.map e.toAddMonoidHom = ⊥ := hm.trans hzero
    exact hS ((AddSubgroup.map_eq_bot_iff_of_injective S e.injective).mp hm0)
end LogicLineages.ModelsAlgebra.PGroups
