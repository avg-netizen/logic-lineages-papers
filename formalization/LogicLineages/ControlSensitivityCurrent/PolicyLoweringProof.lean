module
public import LogicLineages.ControlSensitivityCurrent.PolicyLoweringCalibrationProof
public import LogicLineages.ControlSensitivityCurrent.FullSortProof
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyLowering
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering SourceAdditionCompletion SourceSortCompletion
open PrimitiveLowering.Proof (value_liftPort value_aux)
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

theorem unused_holds (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat) (start : Nat) :
    (∀ e ∈ unused (Γ:=Γ) start, PolicyAddition.Equation p f (extend ρ 9 z) e.1.term e.2.term) ↔
      ∀ i : Fin 9, start ≤ i.val → z i=0 := by
  rw [unused,all_map]
  simp only [port_equation p f hm hi]
  simp only [value_aux]
  simp only [Port.value,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]

theorem sourceExact (p : AdmissibleSum.Policy) (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    {Γ} (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat) :
    SourceHolds p f ρ g z ↔ g.Holds ρ ∧ z = canonicalWitness f ρ g := by
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have hm := hc.1
  have hi : ∀ n : Nat, n ≤ f n := fun n => (hc.2.1 n).le
  have hg := (FullSort.completeSort f hf).1
  have sorted := PairCoding.sortedWitness (fun n => f (n+4)) (fun n => (hg n).1) (fun n => (hg n).2)
  cases g with
  | eq a b =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | add a b c =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | sort a b l h =>
      constructor
      · intro H
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true] at H
        have hs := (sorted
          (a.value ρ) (b.value ρ) (l.value ρ) (h.value ρ) (z 5)).mp
          ⟨by omega,by omega⟩
        refine ⟨⟨hs.1,hs.2.1⟩,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨H,rfl⟩
        have hs := (sorted
          (a.value ρ) (b.value ρ) (l.value ρ) (h.value ρ)
          (max (a.value ρ) (b.value ρ)-min (a.value ρ) (b.value ρ))).mpr ⟨H.1,H.2,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true,canonicalWitness]
        simp
        omega
  | one a =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        have ha : a.value ρ=1 := by omega
        refine ⟨ha,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation p f hm hi,successor_equation p f hm hi,add_equations_exact p f hm hi,successor_identity p f hm hi,value_liftPort,value_aux,unused_holds p f hm hi,true_and,and_true,canonicalWitness]
        simp [Fin.forall_fin_succ,show a.value ρ=1 from h]


theorem sharedInputsAndSyntax : PolicyLoweringTargets.SharedInputsAndSyntax :=
  ⟨PrimitiveLowering.Proof.sharedInputs,PrimitiveLowering.Proof.primitiveRealization⟩
theorem actualFixedSize : PolicyLoweringTargets.ActualFixedSize := PrimitiveLowering.Proof.fixedSize

private theorem graph_term {Γ} (e : Expr Γ) : e.graph.term = e.term :=
  (PrimitiveLowering.Proof.primitiveRealization Γ e).1

theorem allGateExact : PolicyLoweringTargets.AllGateExact := by
  intro f hf p Γ ρ g z
  refine ⟨sourceExact p f hf ρ g z,?_⟩
  rw [← sourceExact p f hf ρ g z]
  unfold ForestHolds SourceHolds forest
  rw [all_map]
  simp only [graph_term]
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyLowering
end LogicLineages.ControlSensitivityCurrent.PolicyLowering
