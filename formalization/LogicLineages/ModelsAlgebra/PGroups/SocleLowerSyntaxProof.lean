module
public import LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormula
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth
open scoped BigOperators

private theorem root_eval (G:Type) [AddCommGroup G] (p j n m:ℕ)
    (a:Fin n→G) (d:Fin m→G) (i:Fin m) :
    (socleRootTerm p j n m i).eval (append a d)=p^j • d i := by
  simp only [socleRootTerm,multiple_term_evaluation G (n+m) (p^j),GroupTerm.eval,append,Fin.addCases_right]
private theorem combination_eval (G:Type) [AddCommGroup G] (p j n m:ℕ)
    (a:Fin n→G) (d:Fin m→G) (r:Fin m→ZMod p) :
    (socleCombinationTerm p j n m r).eval (append a d)=∑i,(r i).val • (p^j • d i) := by
  simp only [socleCombinationTerm,finite_sum_term_evaluation G (n+m) m,
    multiple_term_evaluation G (n+m),root_eval]

theorem socle_lower_matrix_realization : Targets.socleLowerMatrixRealization := by
  classical
  intro p _ G _ j n m a d
  let e := Fintype.equivFin (Fin m→ZMod p)
  simp only [socleLowerMatrix,QF.Realize,finite_conjunction_realization G (n+m) m,
    finite_conjunction_realization G (n+m) (Fintype.card (Fin m→ZMod p)),
    multiple_term_evaluation G (n+m) p,root_eval,GroupTerm.eval]
  constructor
  · rintro ⟨hs,hc⟩
    refine ⟨hs,?_⟩
    intro r hr
    have hh := hc (e r)
    simpa only [e,Equiv.symm_apply_apply,if_neg hr,QF.Realize,combination_eval,GroupTerm.eval] using hh
  · rintro ⟨hs,hc⟩
    refine ⟨hs,?_⟩
    intro k
    by_cases hk:(Fintype.equivFin (Fin m→ZMod p)).symm k=0
    · simp only [if_pos hk,QF.Realize,not_false_eq_true]
    · simpa only [if_neg hk,QF.Realize,combination_eval,GroupTerm.eval] using
        hc ((Fintype.equivFin (Fin m→ZMod p)).symm k) hk

private theorem socle_independence (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G]
    (S:AddSubgroup G) (m:ℕ) (x:Fin m→pSocle p S) :
    LinearIndependent (ZMod p) x ↔ ∀ r:Fin m→ZMod p,r≠0→(∑i,(r i).val • (x i:G))≠0 := by
  have hsum (r:Fin m→ZMod p) :
      ((∑i,r i • x i:pSocle p S):G)=∑i,(r i).val • (x i:G) := by
    have he (i:Fin m) : r i • x i = (r i).val • x i := by
      rw [←Nat.cast_smul_eq_nsmul (ZMod p),ZMod.natCast_zmod_val]
    simp_rw [he]
    change (pSocle p S).subtype (∑i,(r i).val • x i)=_
    rw [map_sum]
    simp only [map_nsmul]
    rfl
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h r hr hz
    have hh : (∑i,r i • x i)=0 := Subtype.ext ((hsum r).trans hz)
    exact hr (funext (h r hh))
  · intro h r hz
    have hr:r=0 := by
      by_contra hn
      exact h r hn ((hsum r).symm.trans (congrArg Subtype.val hz))
    intro i
    simpa only [hr,Pi.zero_apply]

theorem socle_root_representatives : Targets.socleRootRepresentatives := by
  classical
  intro p _ G _ j m
  let S:AddSubgroup G:=finiteFiltration p j
  constructor
  · rintro ⟨d,hs,hc⟩
    let x:Fin m→pSocle p S := fun i=>⟨p^j • d i,⟨by
      change p^j • d i ∈ finiteFiltration p j
      rw [finite_filtration_multiple_image G p j]
      exact ⟨d i,rfl⟩,hs i⟩⟩
    exact ⟨x,(socle_independence p G S m x).mpr hc⟩
  · rintro ⟨x,hx⟩
    have hc := (socle_independence p G S m x).mp hx
    have hroots:∀i:Fin m,∃y:G,p^j • y=(x i:G) := by
      intro i
      have hi := (x i).property.1
      change (x i:G)∈finiteFiltration p j at hi
      exact (finite_filtration_multiple_image G p j).le hi
    choose d hd using hroots
    refine ⟨d,?_,?_⟩
    · intro i
      rw [hd]
      exact (x i).property.2
    · intro r hr
      simpa only [hd] using hc r hr

theorem socle_lower_dimension : Targets.socleLowerDimension := by
  intro p _ j n m
  constructor
  · exact Complexity.sigma one_ne_zero {0} (fun _=>m)
      (fun _=>.qf (socleLowerMatrix p j n m)) (fun _=>0)
      (fun _=>zero_lt_one) (fun _=>Complexity.qf .pi _)
  · intro G _ a
    have he : (socleLowerFormula p j n m).Realize a ↔ ∃d:Fin m→G,SocleRootWitnesses p j d := by
      change (∃i:({0}:Set ℕ),∃d:Fin m→G,(socleLowerMatrix p j n m).Realize (append a d))↔_
      constructor
      · rintro ⟨_,d,hd⟩
        exact ⟨d,(socle_lower_matrix_realization p G j n m a d).mp hd⟩
      · rintro ⟨d,hd⟩
        exact ⟨⟨0,by simp⟩,d,(socle_lower_matrix_realization p G j n m a d).mpr hd⟩
    exact he.trans ((socle_root_representatives p G j m).trans Module.le_rank_iff.symm)
end LogicLineages.ModelsAlgebra.PGroups
