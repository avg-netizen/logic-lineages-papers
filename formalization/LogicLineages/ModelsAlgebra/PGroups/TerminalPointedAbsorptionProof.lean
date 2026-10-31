module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalPointedAbsorptionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SubgroupSumProductProof
public import LogicLineages.ModelsAlgebra.PGroups.SourceAbsorption
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun j => f (append a c j)) = append (fun j => f (a j)) (fun j => f (c j)) := by
  funext j
  induction j using Fin.addCases <;> simp [append]

theorem terminal_pointed_absorption : Targets.terminalPointedAbsorption := by
  classical
  intro G _ _ p _ S K T N b hs hd hN hr hT n a c hac
  have hK : K ≤ S := by rw [hs]; exact le_sup_left
  have hNK : ∀ x : K, p^N • x=0 := by
    intro x
    exact Subtype.ext (congrArg (fun z : S => (z:G)) (hN ⟨x,hK x.property⟩))
  letI : Infinite (finiteFiltration p b : AddSubgroup K) := infinite_ulm_infinite_filtration p K b hr
  have hb : b<N := by
    by_contra h
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (le_of_not_gt h)
    have hz : ∀ x : K, p^b • x=0 := by
      intro x
      rw [hj,pow_add,mul_nsmul,hNK,nsmul_zero]
    obtain ⟨x,hx⟩ := exists_ne (0:(finiteFiltration p b : AddSubgroup K))
    obtain ⟨y,hy⟩ := (finite_filtration_multiple_image K p b).le x.property
    change p^b • y = (x:K) at hy
    exact hx (Subtype.ext (hy.symm.trans (hz y)))
  obtain ⟨A,inst,hcount,⟨e⟩⟩ := single_reservoir_extraction p K N ⟨b,hb⟩ hNK hr
  letI := inst
  obtain ⟨es,hes⟩ := subgroup_sum_product G S K T hs hd
  let i : K →+ S := AddSubgroup.inclusion hK
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z:S => (z:G)) h)
  have he (x:K) : es (x,0)=i x := by
    apply Subtype.ext
    change (es (x,0):G) = (x:G)
    simpa only [ZeroMemClass.coe_zero,add_zero] using hes x 0
  have hfix : ∀ (m:ℕ) (v:Fin m→K), ∃ f:S→+K,
      Function.Injective f ∧ ∀ j, f (i (v j))=v j := by
    intro m v
    obtain ⟨f,hf,hfv⟩ := absorption_tuple_transport p K A T (b+1) e hT m v
    refine ⟨f.comp es.symm.toAddMonoidHom,hf.comp es.symm.injective,?_⟩
    intro j
    change f (es.symm (i (v j)))=v j
    rw [← he,es.symm_apply_apply,hfv]
  have ha : a=fun j=>i (c j) := by
    funext j
    exact Subtype.ext (hac j)
  rw [ha]
  have hh : BackAndForth ((1:Ordinal.{0})+1) (fun j=>i (c j)) c := by
    apply (back_forth_successor 1 S K n _ _).mpr
    intro m d
    refine ⟨fun j=>i (d j),?_⟩
    simpa only [hom_append] using tuple_fixing_backforth_one S K i hi hfix (n+m) (append c d)
  simpa only [one_add_one_eq_two] using hh
end LogicLineages.ModelsAlgebra.PGroups
