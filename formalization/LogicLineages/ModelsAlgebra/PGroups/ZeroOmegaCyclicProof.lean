module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroOmegaCyclicTargets
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmProof
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationProof
public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlm
public import LogicLineages.ModelsAlgebra.PGroups.CyclicFiltration
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmProof
public import Mathlib.Data.DFinsupp.Encodable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

private theorem diagonal_cardinal_sum (I:ℕ→Type) (n:ℕ) :
    Cardinal.sum (fun i:Σm:ℕ,I m=>if n+1=i.1+1 then (1:Cardinal) else 0)=Cardinal.mk (I n) := by
  classical
  let F:(Σm:ℕ,I m)→Type:=fun i=>Fin (if n+1=i.1+1 then 1 else 0)
  have level:(∀z:(Σi:Σm:ℕ,I m,F i),z.1.1=n):=by
    rintro ⟨⟨m,i⟩,k⟩
    have h:n+1=m+1:=by
      by_contra h
      have hk:k.val<0:=by simpa only [F,if_neg h] using k.isLt
      exact Nat.not_lt_zero _ hk
    exact Nat.succ.inj h.symm
  let value:(Σi:Σm:ℕ,I m,F i)→I n:=fun z=>(level z) ▸ z.1.2
  let embed:I n→(Σi:Σm:ℕ,I m,F i):=fun i=>⟨⟨n,i⟩,⟨0,by simp [F]⟩⟩
  let e:(Σi:Σm:ℕ,I m,F i)≃I n:=
    { toFun:=value
      invFun:=embed
      left_inv:=by
        rintro ⟨⟨m,i⟩,k⟩
        have hm:m=n:=level ⟨⟨m,i⟩,k⟩
        subst m
        apply Sigma.ext
        · simp only [value,embed]
        · apply heq_of_eq
          apply Fin.ext
          change 0=k.val
          have hk:k.val<1:=by simpa only [F,if_pos rfl,ite_true] using k.isLt
          omega
      right_inv:=by
        intro i
        simp only [value,embed] }
  calc
    Cardinal.sum (fun i:Σm:ℕ,I m=>if n+1=i.1+1 then (1:Cardinal) else 0)=
        Cardinal.sum (fun i=>Cardinal.mk (F i)):=by
      congr 1
      funext i
      by_cases h:n+1=i.1+1 <;> simp [F,h]
    _=Cardinal.mk (Σi:Σm:ℕ,I m,F i):=(Cardinal.mk_sigma F).symm
    _=Cardinal.mk (I n):=Cardinal.mk_congr e

theorem zero_omega_cyclic_sum_calibration : Targets.zeroOmegaCyclicSumCalibration := by
  classical
  intro p _ I _
  letI:∀i:Σn:ℕ,I n,NeZero (p^(i.1+1)):=fun _=>⟨pow_ne_zero _ (Fact.out:p.Prime).ne_zero⟩
  let H:=ZeroOmegaCyclicSum p I
  have hc:Countable H:=by
    change Countable (Π₀i:Σn:ℕ,I n,ZMod (p^(i.1+1)))
    infer_instance
  have hp:∀x:H,∃k:ℕ,p^k • x=0:=by
    intro x
    induction x using DirectSum.induction_on with
    | zero=>exact ⟨0,by simp⟩
    | of i x=>
      have hx:p^(i.1+1) • x=0:=by rw [nsmul_eq_mul,ZMod.natCast_self,zero_mul]
      exact ⟨i.1+1,by rw [←map_nsmul,hx,map_zero]⟩
    | add x y hx hy=>
      obtain ⟨n,hn⟩:=hx
      obtain ⟨m,hm⟩:=hy
      refine ⟨n+m,?_⟩
      rw [nsmul_add]
      have hn':p^(n+m) • x=0:=by rw [pow_add,mul_nsmul,hn,nsmul_zero]
      have hm':p^(n+m) • y=0:=by rw [Nat.add_comm n m,pow_add,mul_nsmul,hm,nsmul_zero]
      rw [hn',hm',zero_add]
  have hz:(transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):AddSubgroup H)=⊥:=by
    rw [transfinite_direct_sum]
    apply le_antisymm _ bot_le
    intro x hx
    apply DirectSum.ext
    intro i
    have hxi:=(direct_sum_subgroup_coordinates _ x).mp hx i
    have hi:(transfiniteFiltration p ((i.1+1:ℕ):Ordinal.{0}):AddSubgroup (ZMod (p^(i.1+1))))=⊥:=by
      rw [finite_ordinal_filtration]
      exact cyclic_filtration_bottom p (i.1+1) (i.1+1) le_rfl
    have hz':(transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):AddSubgroup (ZMod (p^(i.1+1))))=⊥:=
      le_antisymm ((transfiniteFiltration_antitone p (Ordinal.natCast_lt_omega0 (i.1+1)).le).trans hi.le) bot_le
    rw [hz',AddSubgroup.mem_bot] at hxi
    exact hxi
  refine ⟨hc,hp,hz,?_⟩
  intro n
  rw [transfinite_direct_sum_ulm_rank]
  have hcyc:∀i:Σm:ℕ,I m,
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup (ZMod (p^(i.1+1)))))=
        if n+1=i.1+1 then 1 else 0:=by
    intro i
    rw [finite_ordinal_filtration]
    exact cyclic_ulm_rank p (i.1+1) n
  simp_rw [hcyc]
  exact diagonal_cardinal_sum I n

theorem countable_zero_omega_cyclic_decomposition : Targets.countableZeroOmegaCyclicDecomposition := by
  classical
  intro p _ G _ _ hG hz
  let V:ℕ→Type:=fun n=>UlmLayer p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup G)
  let I:ℕ→Type:=fun n=>Module.Basis.ofVectorSpaceIndex (ZMod p) (V n)
  let b:∀n:ℕ,Module.Basis (I n) (ZMod p) (V n):=fun _=>Module.Basis.ofVectorSpace _ _
  have hI:∀n,Countable (I n):=by
    intro n
    letI:Countable (V n):=(QuotientAddGroup.mk'_surjective
      (successorSocleSubgroup p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup G))).countable
    exact (b n).injective.countable
  letI:=hI
  have hd:=zero_omega_cyclic_sum_calibration p I
  letI:Countable (ZeroOmegaCyclicSum p I):=hd.1
  have hr:∀n:ℕ,Cardinal.mk (I n)=Module.rank (ZMod p) (V n):=fun n=>(b n).mk_eq_rank''
  refine ⟨I,hI,?_,hr⟩
  apply countable_ulm_at_zero_cut G (ZeroOmegaCyclicSum p I) p hG hd.2.1 Ordinal.omega0
    Ordinal.isSuccLimit_omega0 hz hd.2.2.1
  intro α hα
  obtain ⟨n,rfl⟩:=Ordinal.lt_omega0.mp hα
  exact (hr n).symm.trans (hd.2.2.2 n).symm
end LogicLineages.ModelsAlgebra.PGroups
