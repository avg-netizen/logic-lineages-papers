module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringSemanticProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof
open SourceAdditionCompletion SourceSortCompletion
attribute [local irreducible] Phi actualCollapse successorObservation

theorem all_append {α : Type} (P : α → Prop) (xs ys : List α) :
    (∀ x ∈ xs++ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),fun x hx => h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hx,hy⟩ x h
    rcases List.mem_append.mp h with h|h
    · exact hx x h
    · exact hy x h

theorem all_cons {α : Type} (P : α → Prop) (x : α) (xs : List α) :
    (∀ a ∈ x::xs, P a) ↔ P x ∧ (∀ a ∈ xs, P a) := by simp only [List.mem_cons,forall_eq_or_imp]

theorem all_nil {α : Type} (P : α → Prop) : (∀ a ∈ ([] : List α), P a) ↔ True := by simp

theorem all_map {α β : Type} (P : β → Prop) (f : α → β) (xs : List α) :
    (∀ y ∈ xs.map f, P y) ↔ ∀ x ∈ xs, P (f x) := by
  constructor
  · intro h x hx
    exact h (f x) (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact h x hx

theorem unused_holds {Γ} (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat) (start : Nat) :
    (∀ e ∈ unused (Γ:=Γ) start, Equation (extend ρ 9 z) e.1.term e.2.term) ↔
      ∀ i : Fin 9, start ≤ i.val → z i=0 := by
  rw [unused,all_map]
  simp only [port_equation]
  simp only [value_aux]
  simp only [Port.value,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]

theorem sourceExact : Targets.SourceExact := by
  intro Γ ρ g z
  cases g with
  | eq a b =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | add a b c =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | sort a b l h =>
      constructor
      · intro H
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true] at H
        have hs := (SourceSuccessorCodingProof.successorSortedWitness
          (a.value ρ) (b.value ρ) (l.value ρ) (h.value ρ) (z 5)).mp
          ⟨by omega,by omega⟩
        refine ⟨⟨hs.1,hs.2.1⟩,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨H,rfl⟩
        have hs := (SourceSuccessorCodingProof.successorSortedWitness
          (a.value ρ) (b.value ρ) (l.value ρ) (h.value ρ)
          (max (a.value ρ) (b.value ρ)-min (a.value ρ) (b.value ρ))).mpr ⟨H.1,H.2,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true,canonicalWitness]
        simp
        omega
  | one a =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        have ha : a.value ρ=1 := by omega
        refine ⟨ha,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation,successor_equation,add_equations_exact,successor_identity,value_liftPort,value_aux,unused_holds,true_and,and_true,canonicalWitness]
        simp [Fin.forall_fin_succ,show a.value ρ=1 from h]

@[simp] theorem graph_term {Γ} (e : Expr Γ) : e.graph.term=e.term :=
  (primitiveRealization Γ e).1

theorem graphExact : Targets.GraphExact := by
  intro Γ ρ g z
  rw [← sourceExact Γ ρ g z]
  unfold forest SourceHolds
  rw [all_map]
  simp only [graph_term]
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof
