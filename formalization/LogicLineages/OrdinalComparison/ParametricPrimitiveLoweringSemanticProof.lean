module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringTargets
public import LogicLineages.OrdinalComparison.ParametricSourceOneProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Proof
open PrimitiveLowering SourceAdditionCompletion SourceSortCompletion
open ParametricSourceSuccessor
variable (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat,n ≤ G n)

theorem port_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Port Γ) :
    ParametricSourceAddition.Equation G ρ (Expr.port a).term (Expr.port b).term ↔
      a.value ρ = b.value ρ := by
  have ha := PrimitiveLowering.Proof.port_assignment a
  have hb := PrimitiveLowering.Proof.port_assignment b
  have hva : denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal))
      (PrimitiveLowering.Proof.portExpression a) = ((a.value ρ+1 : Nat) : Ordinal) := by
    cases a <;> simp [PrimitiveLowering.Proof.portExpression,Port.value,denoteWith,input]
  have hvb : denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal))
      (PrimitiveLowering.Proof.portExpression b) = ((b.value ρ+1 : Nat) : Ordinal) := by
    cases b <;> simp [PrimitiveLowering.Proof.portExpression,Port.value,denoteWith,input]
  constructor
  · rintro ⟨va,vb,hva',hvb',he⟩
    have ea := Option.some.inj (ha.symm.trans hva')
    have eb := Option.some.inj (hb.symm.trans hvb')
    cases ea
    cases eb
    rw [hva,hvb] at he
    have hn := Nat.cast_injective he
    omega
  · intro he
    exact ⟨_,_,ha,hb,by rw [hva,hvb,he]⟩

include hm hi in
theorem erase_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    ParametricSourceAddition.Equation G ρ (Expr.erase a b).term (Expr.erase c d).term ↔
      3*a.value ρ+b.value ρ=3*c.value ρ+d.value ρ := by
  exact ParametricSourceAddition.Proof.weighted_equality G hm hi ρ a b c d

include hm hi in
theorem add_equations_exact {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    (∀ e ∈ addEquations a b c d, ParametricSourceAddition.Equation G ρ e.1.term e.2.term) ↔
      a.value ρ+b.value ρ=c.value ρ ∧ d.value ρ=3*b.value ρ := by
  simp [addEquations,erase_equation G hm hi,Port.value]
  omega

include hm hi in
theorem successor_aux_identity {Γ} (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat) :
    ParametricSourceAddition.Equation G (extend ρ 9 z)
      (Expr.successor (aux 0)).term Expr.identityZero.term ↔ z 0=2 := by
  have h := (ParametricSourceOne.Proof.identitySourceEquation.2 G hm hi
    (Block Γ) (extend ρ 9 z) (fresh (0 : Fin 9)))
  simpa only [Expr.term,aux,SourceAdditionCompletion.Atom.term,successorProbe,
    input,PrimitiveLowering.Proof.extend_fresh] using h

theorem all_append {α : Type} (P : α → Prop) (xs ys : List α) :
    (∀ x ∈ xs++ys,P x) ↔ (∀ x ∈ xs,P x) ∧ (∀ x ∈ ys,P x) := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),fun x hx => h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hx,hy⟩ x h
    rcases List.mem_append.mp h with h|h
    · exact hx x h
    · exact hy x h
theorem all_cons {α : Type} (P : α → Prop) (x : α) (xs : List α) :
    (∀ a ∈ x::xs,P a) ↔ P x ∧ (∀ a ∈ xs,P a) := by simp
theorem all_nil {α : Type} (P : α → Prop) : (∀ a ∈ ([] : List α),P a) ↔ True := by simp
theorem all_map {α β : Type} (P : β → Prop) (f : α → β) (xs : List α) :
    (∀ y ∈ xs.map f,P y) ↔ ∀ x ∈ xs,P (f x) := by simp

theorem unused_holds {Γ} (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat) (start : Nat) :
    (∀ e ∈ unused (Γ:=Γ) start,ParametricSourceAddition.Equation G (extend ρ 9 z) e.1.term e.2.term) ↔
      ∀ i : Fin 9,start ≤ i.val → z i=0 := by
  rw [unused,all_map]
  simp only [port_equation G,PrimitiveLowering.Proof.value_aux]
  simp only [Port.value,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Proof
