module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferDirectSumTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem pruefer_direct_sum_nature : Targets.prueferDirectSumNature := by
  classical
  intro p _ I
  constructor
  · intro n hn x
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0,nsmul_zero n⟩
    | add x y hx hy =>
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := hy
      exact ⟨a+b,by rw [nsmul_add,ha,hb]⟩
    | single i x =>
      obtain ⟨y,hy⟩ := (genuine_pruefer_model p).2.1 n hn x
      refine ⟨Finsupp.single i y,?_⟩
      change n • (Finsupp.singleAddHom i) y = (Finsupp.singleAddHom i) x
      rw [←map_nsmul,hy]
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0,nsmul_zero _⟩
    | single i x =>
      obtain ⟨k,hk⟩ := (genuine_pruefer_model p).1 x
      refine ⟨k,?_⟩
      change p^k • (Finsupp.singleAddHom i) x = 0
      rw [←map_nsmul,hk,map_zero]
    | add x y hx hy =>
      obtain ⟨k,hk⟩ := hx
      obtain ⟨j,hj⟩ := hy
      refine ⟨k+j,?_⟩
      rw [nsmul_add]
      have h1 : p^(k+j) • x=0 := by rw [pow_add,mul_nsmul,hk,nsmul_zero]
      have h2 : p^(k+j) • y=0 := by rw [Nat.add_comm k j,pow_add,mul_nsmul,hj,nsmul_zero]
      rw [h1,h2,add_zero]

theorem pruefer_direct_sum_socle : Targets.prueferDirectSumSocle := by
  classical
  intro p _ I e
  let h : ZMod p →+ PrueferModel p := (pSocle p (⊤ : AddSubgroup (PrueferModel p))).subtype.comp e.toAddMonoidHom
  let f : (I→₀ZMod p) →+ PrueferDirectSum p I := Finsupp.mapRange.addMonoidHom h
  have hf (x:I→₀ZMod p) : f x ∈ pSocle p (⊤ : AddSubgroup (PrueferDirectSum p I)) := by
    refine ⟨AddSubgroup.mem_top _,?_⟩
    change p • f x = 0
    apply Finsupp.ext
    intro i
    change p • (e (x i):PrueferModel p) = 0
    exact (e (x i)).property.2
  let g := f.codRestrict (pSocle p (⊤ : AddSubgroup (PrueferDirectSum p I))) hf
  have hi : Function.Injective g := by
    intro x y heq
    apply Finsupp.ext
    intro i
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun z:pSocle p (⊤ : AddSubgroup (PrueferDirectSum p I)) => (z:PrueferDirectSum p I) i) heq
  have hs : Function.Surjective g := by
    intro x
    let v (i:I) : pSocle p (⊤ : AddSubgroup (PrueferModel p)) :=
      ⟨(x:PrueferDirectSum p I) i,AddSubgroup.mem_top _,
        congrArg (fun z:PrueferDirectSum p I => z i) x.property.2⟩
    let c : I→₀ZMod p := Finsupp.onFinset (x:PrueferDirectSum p I).support
      (fun i=>e.symm (v i)) (by
        intro i hi
        apply Finsupp.mem_support_iff.mpr
        intro hz
        apply hi
        have hv : v i = 0 := Subtype.ext hz
        rw [hv,e.symm.map_zero])
    refine ⟨c,Subtype.ext ?_⟩
    apply Finsupp.ext
    intro i
    change (e (c i):PrueferModel p) = (x:PrueferDirectSum p I) i
    change (e (e.symm (v i)):PrueferModel p) = _
    rw [e.apply_symm_apply]
  let d := AddEquiv.ofBijective g ⟨hi,hs⟩
  refine ⟨d.symm,?_⟩
  intro x i
  exact congrArg (fun z:pSocle p (⊤ : AddSubgroup (PrueferDirectSum p I)) => (z:PrueferDirectSum p I) i) (d.apply_symm_apply x)
end LogicLineages.ModelsAlgebra.PGroups
