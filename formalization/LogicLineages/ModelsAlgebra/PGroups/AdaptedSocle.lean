module

public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmBasisLift
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open Function

private theorem filtration_anti (p : ℕ) (G : Type) [AddCommGroup G] :
    Antitone (fun j => (finiteFiltration p j : AddSubgroup G)) := by
  apply antitone_nat_of_succ_le
  intro j
  rintro z ⟨y,hy,rfl⟩
  exact (finiteFiltration p j : AddSubgroup G).nsmul_mem hy p

private theorem inclusion_injective (p : ℕ) (G : Type) [AddCommGroup G] (S : AddSubgroup G) :
    Function.Injective (socleInclusion p S) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : pSocle p (⊤ : AddSubgroup G) => (z : G)) h)

private theorem inclusion_mem_level (p : ℕ) (G : Type) [AddCommGroup G] (j l : ℕ)
    (h : j ≤ l) (z : pSocle p (finiteFiltration p l : AddSubgroup G)) :
    socleInclusion p (finiteFiltration p l) z ∈ socleLevel p G j :=
  filtration_anti p G h z.property.1

private theorem level_independent (p : ℕ) (G : Type) [AddCommGroup G] (j : ℕ) (I : Type)
    (b : Module.Basis I (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)))
    (x : I → pSocle p (finiteFiltration p j : AddSubgroup G))
    (hx : ∀ i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j)) (x i) = b i) :
    LinearIndependent (ZMod p) (fun i => socleInclusion p (finiteFiltration p j) (x i)) := by
  let q := (QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G))).toZModLinearMap p
  have hq : q ∘ x = b := funext hx
  have hi : LinearIndependent (ZMod p) x := LinearIndependent.of_comp q (by rw [hq]; exact b.linearIndependent)
  exact hi.map' (socleInclusion p (finiteFiltration p j))
    (LinearMap.ker_eq_bot.mpr (inclusion_injective p G _))

private theorem level_disjoint (p : ℕ) (G : Type) [AddCommGroup G] (j : ℕ) (I : Type)
    (b : Module.Basis I (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)))
    (x : I → pSocle p (finiteFiltration p j : AddSubgroup G))
    (hx : ∀ i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j)) (x i) = b i) :
    Disjoint (Submodule.span (ZMod p) (Set.range (fun i => socleInclusion p (finiteFiltration p j) (x i))))
      (socleLevel p G (j+1)) := by
  classical
  apply Submodule.disjoint_def.mpr
  intro z hz hznext
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  let v := Finsupp.linearCombination (ZMod p) x c
  let inc := socleInclusion p (finiteFiltration p j : AddSubgroup G)
  have hv : inc v = z := by
    rw [Finsupp.apply_linearCombination]
    exact hc
  let q := (QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G))).toZModLinearMap p
  have hq : q ∘ x = b := funext hx
  have hzero : q v = 0 := by
    apply (QuotientAddGroup.eq_zero_iff v).mpr
    refine ⟨?_, v.property.2⟩
    have he : (v : G) = (z : G) := congrArg (fun w : pSocle p (⊤ : AddSubgroup G) => (w : G)) hv
    change (v : G) ∈ finiteFiltration p (j+1)
    rw [he]
    exact hznext
  have hc0 : c = 0 := by
    apply (linearIndependent_iff.mp b.linearIndependent) c
    change q (Finsupp.linearCombination (ZMod p) x c) = 0 at hzero
    rw [Finsupp.apply_linearCombination, hq] at hzero
    exact hzero
  rw [← hv]
  dsimp only [v]
  rw [hc0, map_zero, map_zero]

private def sumFiberEquiv {N : ℕ} (I : Fin (N+1) → Type) :
    (I 0 ⊕ (Σ l : Fin N, I l.succ)) ≃ (Σ l : Fin (N+1), I l) where
  toFun := Sum.elim (Sigma.mk 0) (fun a => ⟨a.1.succ,a.2⟩)
  invFun a := Fin.cases (fun i => Sum.inl i) (fun l i => Sum.inr ⟨l,i⟩) a.1 a.2
  left_inv := by rintro (i | ⟨l,i⟩) <;> rfl
  right_inv := by rintro ⟨l,i⟩; cases l using Fin.cases <;> rfl

private theorem ordered_independent (p : ℕ) (G : Type) [AddCommGroup G] :
    ∀ (N : ℕ) (f : Fin N → ℕ), StrictMono f → ∀ (I : Fin N → Type)
    (b : ∀ l, Module.Basis (I l) (ZMod p) (UlmLayer p (finiteFiltration p (f l) : AddSubgroup G)))
    (x : ∀ l, I l → pSocle p (finiteFiltration p (f l) : AddSubgroup G)),
    (∀ l i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p (f l))) (x l i) = b l i) →
    LinearIndependent (ZMod p) (fun a : Σ l : Fin N, I l => socleInclusion p (finiteFiltration p (f a.1)) (x a.1 a.2)) := by
  intro N
  induction N with
  | zero => intro f hf I b x hx; exact linearIndependent_empty_type
  | succ N ih =>
    intro f hf I b x hx
    have ht := ih (fun l => f l.succ) (fun a b h => hf (by change a.val + 1 < b.val + 1; omega))
      (fun l => I l.succ) (fun l => b l.succ) (fun l => x l.succ) (fun l => hx l.succ)
    have hh := level_independent p G (f 0) (I 0) (b 0) (x 0) (hx 0)
    have hle : Submodule.span (ZMod p)
        (Set.range (fun a : Σ l : Fin N, I l.succ => socleInclusion p (finiteFiltration p (f a.1.succ)) (x a.1.succ a.2))) ≤
        socleLevel p G (f 0 + 1) := by
      apply Submodule.span_le.mpr
      rintro z ⟨a,rfl⟩
      apply inclusion_mem_level
      exact hf (by simp)
    have hs := hh.sum_type ht ((level_disjoint p G (f 0) (I 0) (b 0) (x 0) (hx 0)).mono_right hle)
    apply (linearIndependent_equiv (sumFiberEquiv I)).mp
    have heq : ((fun a : Σ l : Fin (N+1), I l =>
        socleInclusion p (finiteFiltration p (f a.1)) (x a.1 a.2)) ∘ sumFiberEquiv I) =
        Sum.elim (fun i => socleInclusion p (finiteFiltration p (f 0)) (x 0 i))
          (fun a : Σ l : Fin N, I l.succ =>
            socleInclusion p (finiteFiltration p (f a.1.succ)) (x a.1.succ a.2)) := by
      funext a
      cases a <;> rfl
    rw [heq]
    exact hs

theorem adapted_socle_independent : Targets.groupAdaptedSocleIndependent := by
  intro p _ G _ N I b x hx
  exact ordered_independent p G N (fun l => l.val) (fun _ _ h => h) I b x hx

theorem adapted_socle_filtered_span : Targets.groupAdaptedSocleFilteredSpan := by
  classical
  intro p _ G _ N hbound I b x hx
  let T (j : ℕ) := Submodule.span (ZMod p)
    (Set.range (fun a : {a : (Σ l : Fin N, I l) // j ≤ a.1.val} => includedSocleFamily p N I x a.val))
  have hmono (j : ℕ) : T (j+1) ≤ T j := by
    apply Submodule.span_le.mpr
    rintro z ⟨a,rfl⟩
    exact Submodule.subset_span ⟨⟨a.val, (Nat.le_succ j).trans a.property⟩, rfl⟩
  have hlower : ∀ j : ℕ, j ≤ N → socleLevel p G j ≤ T j := by
    intro j hj
    apply Nat.decreasingInduction (n := N) (motive := fun l _ => socleLevel p G l ≤ T l) ?_ ?_ hj
    · intro l hl ih z hz
      let a : Fin N := ⟨l,hl⟩
      let z' : pSocle p (finiteFiltration p l : AddSubgroup G) := ⟨z.val, ⟨hz,z.property.2⟩⟩
      let q := (QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p l : AddSubgroup G))).toZModLinearMap p
      let c := (b a).repr (q z')
      let v := Finsupp.linearCombination (ZMod p) (x a) c
      let inc := socleInclusion p (finiteFiltration p l : AddSubgroup G)
      have hq : q ∘ x a = b a := funext (hx a)
      have he : q v = q z' := by
        rw [Finsupp.apply_linearCombination, hq]
        exact (b a).linearCombination_repr (q z')
      have hd : z - inc v ∈ socleLevel p G (l+1) := by
        have hk : q (z' - v) = 0 := by rw [map_sub, he, sub_self]
        have hm := (QuotientAddGroup.eq_zero_iff (z' - v)).mp hk
        exact hm.1
      have hv : inc v ∈ T l := by
        rw [Finsupp.apply_linearCombination]
        apply (Submodule.span_le.mpr (show Set.range (inc ∘ x a) ⊆ T l from ?_))
        · rw [← Finsupp.range_linearCombination]
          exact ⟨c,rfl⟩
        · rintro w ⟨i,rfl⟩
          exact Submodule.subset_span ⟨⟨⟨a,i⟩,le_rfl⟩,rfl⟩
      have hadd := (T l).add_mem (hmono l (ih hd)) hv
      simpa only [sub_add_cancel] using hadd
    · intro z hz
      obtain ⟨y,hy⟩ := (finite_filtration_multiple_image G p N).le hz
      have hz0 : z = 0 := Subtype.ext (hy.symm.trans (hbound y))
      rw [hz0]
      exact (T N).zero_mem
  intro j hj
  apply le_antisymm (hlower j hj)
  apply Submodule.span_le.mpr
  rintro z ⟨a,rfl⟩
  exact inclusion_mem_level p G j a.val.1.val a.property (x a.val.1 a.val.2)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
