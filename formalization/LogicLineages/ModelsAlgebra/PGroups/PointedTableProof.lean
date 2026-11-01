module
public import LogicLineages.ModelsAlgebra.PGroups.PointedTableTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTable
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenaming
public import LogicLineages.ModelsAlgebra.PGroups.Relativized
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleWindowProof
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem pointed_matrix (K:Type) [AddCommGroup K] [Fintype K]
    (n m:ℕ) (a:Fin m→K) (t:Fin m→GroupTerm n)
    (G:Type) [AddCommGroup G] (b:Fin n→G) (d:Fin (Fintype.card K)→G) :
    (pointedTableMatrix K n m a t).Realize (append b d) ↔
      let value:K→G := fun x=>d (Fintype.equivFin K x)
      Function.Injective value ∧ value 0=0 ∧ (∀x, value (-x) = -value x) ∧
        (∀x y,value (x+y)=value x+value y) ∧ ∀i,value (a i)=(t i).eval b := by
  have hr:∀i, (renameTerm (Fin.castAdd (Fintype.card K)) (t i)).eval (append b d)=(t i).eval b := by
    intro i
    rw [term_renaming_evaluation]
    simp only [append,Fin.addCases_left]
  simp only [pointedTableMatrix,QF.Realize,
    finite_image_table_matrix K G 1 n b d,one_nsmul,
    finite_conjunction_realization G (n+Fintype.card K) m,
    table_term_evaluation K G 1 n b d,hr]
  tauto

theorem pointed_finite_table_relative_correct : Targets.pointedFiniteTableRelativeCorrect := by
  classical
  intro K _ _ n m a t G _ S b
  let e:=Fintype.equivFin K
  change (∃i:({0}:Set ℕ),∃d:Fin (Fintype.card K)→S,
    (pointedTableMatrix K n m a t).Realize (append b (fun i=>(d i:G)))) ↔ _
  constructor
  · rintro ⟨_,d,hd⟩
    have hv := (pointed_matrix K n m a t G b (fun i=>(d i:G))).mp hd
    let f:K→+S :=
      { toFun:=fun x=>d (e x)
        map_zero':=Subtype.ext hv.2.1
        map_add':=fun x y=>Subtype.ext (hv.2.2.2.1 x y) }
    refine ⟨f,?_,?_⟩
    · intro x y h
      exact hv.1 (congrArg Subtype.val h)
    · exact hv.2.2.2.2
  · rintro ⟨f,hf,ha⟩
    let d:Fin (Fintype.card K)→S := fun i=>f (e.symm i)
    have hvalue:∀x:K,(d (Fintype.equivFin K x):G)=(f x:G) := by
      intro x
      simp only [d,e,Equiv.symm_apply_apply]
    refine ⟨⟨0,by simp⟩,d,(pointed_matrix K n m a t G b _).mpr ?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro x y h
      apply hf
      apply Subtype.ext
      simpa only [hvalue] using h
    · dsimp only
      rw [hvalue]
      exact congrArg Subtype.val f.map_zero
    · intro x
      dsimp only
      rw [hvalue,hvalue]
      exact congrArg Subtype.val (f.map_neg x)
    · intro x y
      dsimp only
      rw [hvalue,hvalue,hvalue]
      exact congrArg Subtype.val (f.map_add x y)
    · intro i
      dsimp only
      rw [hvalue]
      exact ha i

theorem pointed_finite_table_correct : Targets.pointedFiniteTableCorrect := by
  classical
  intro K _ _ n m a t
  refine ⟨Complexity.sigma one_ne_zero {0} (fun _=>Fintype.card K)
    (fun _=>.qf (pointedTableMatrix K n m a t)) (fun _=>0)
    (fun _=>zero_lt_one) (fun _=>Complexity.qf .pi _),?_⟩
  intro G _ b
  rw [←relativized_top_agreement G n (pointedTableFormula K n m a t) b,
    pointed_finite_table_relative_correct K n m a t G ⊤ b]
  constructor
  · rintro ⟨f,hf,ha⟩
    exact ⟨(⊤:AddSubgroup G).subtype.comp f,Subtype.val_injective.comp hf,ha⟩
  · rintro ⟨f,hf,ha⟩
    let j:K→+(⊤:AddSubgroup G) := f.codRestrict ⊤ (fun _=>AddSubgroup.mem_top _)
    refine ⟨j,?_,ha⟩
    intro x y h
    exact hf (congrArg Subtype.val h)

theorem finite_socle_sigma_one_orbits : Targets.finiteSocleSigmaOneOrbits := by
  classical
  intro G _ _ p _ _ hG n a
  let A:=AddSubgroup.closure (Set.range a)
  letI:Finite A := p_primary_finite_tuple_closure G p (Fact.out:p.Prime).ne_zero hG n a
  obtain ⟨B,hB,hAB,hwindow⟩ := finite_socle_embedding_window G p hG A
  letI:Finite B := hB
  letI:Fintype B := Fintype.ofFinite B
  let aB:Fin n→B := fun i=>⟨a i,hAB (AddSubgroup.subset_closure ⟨i,rfl⟩)⟩
  let ts:Fin n→GroupTerm n := fun i=>.var i
  obtain ⟨hc,hsem⟩ := pointed_finite_table_correct B n n aB ts
  refine ⟨pointedTableFormula B n n aB ts,hc,?_⟩
  intro b
  rw [hsem G b]
  constructor
  · rintro ⟨f,hf,ha⟩
    obtain ⟨u,hu⟩ := hwindow f hf
    refine ⟨u,?_⟩
    intro i
    exact (hu ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩).trans (ha i)
  · rintro ⟨u,hu⟩
    exact ⟨u.toAddMonoidHom.comp B.subtype,u.injective.comp Subtype.val_injective,hu⟩
end LogicLineages.ModelsAlgebra.PGroups
