module
public import LogicLineages.ModelsAlgebra.PGroups.RelativizedTargets
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

private theorem coe_append {G : Type*} [AddCommGroup G] (S : AddSubgroup G)
    {n m : ℕ} (a : Fin n → S) (c : Fin m → S) :
    (fun j => ((append a c j : S) : G)) = append (fun j => (a j : G)) (fun j => (c j : G)) := by
  funext j
  induction j using Fin.addCases <;> simp [append]

theorem relativized_top_agreement : Targets.groupRelativizedTopAgreement := by
  intro G _ n φ
  induction φ with
  | qf q => intro a; rfl
  | disjEx s m matrix ih =>
    intro a
    constructor
    · rintro ⟨i,c,hc⟩
      exact ⟨i,fun j => (c j : G),(ih i _).mp hc⟩
    · rintro ⟨i,c,hc⟩
      exact ⟨i,fun j => ⟨c j,AddSubgroup.mem_top _⟩,(ih i _).mpr hc⟩
  | conjAll s m matrix ih =>
    intro a
    constructor
    · intro h i c
      exact (ih i _).mp (h i (fun j => ⟨c j,AddSubgroup.mem_top _⟩))
    · intro h i c
      exact (ih i _).mpr (h i (fun j => (c j : G)))

theorem relativized_subgroup_agreement : Targets.groupRelativizedSubgroupAgreement := by
  intro G _ S n φ
  induction φ with
  | qf q =>
    intro a
    exact (qf_truth_agreement S G _ a (fun j => (a j : G))
      (embedding_atomic_agreement S G S.subtype Subtype.val_injective _ a) q).symm
  | disjEx s m matrix ih =>
    intro a
    change (∃ i, ∃ c : Fin (m i) → S, (matrix i).RealizeIn S
      (append (fun j => (a j : G)) (fun j => (c j : G)))) ↔ _
    apply exists_congr
    intro i
    apply exists_congr
    intro c
    simpa only [coe_append] using ih i (append a c)
  | conjAll s m matrix ih =>
    intro a
    change (∀ i, ∀ c : Fin (m i) → S, (matrix i).RealizeIn S
      (append (fun j => (a j : G)) (fun j => (c j : G)))) ↔ _
    apply forall_congr'
    intro i
    apply forall_congr'
    intro c
    simpa only [coe_append] using ih i (append a c)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
