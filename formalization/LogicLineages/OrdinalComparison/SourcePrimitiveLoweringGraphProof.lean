module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof

@[simp] theorem extend_shift {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (n : Nat) (z : Fin n → Nat) {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level+1)) :
    extend ρ n z ⟨τ,shift n x,j⟩ = ρ ⟨τ,x,j⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun i => z i.succ)

@[simp] theorem extend_fresh {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (n : Nat) (z : Fin n → Nat) (i : Fin n) :
    extend ρ n z ⟨.ground,fresh i,0⟩ = z i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · rfl
      · exact ih (fun j => z j.succ) k

@[simp] theorem value_liftPort {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (z : Fin 9 → Nat) (a : Port Γ) :
    Port.value (extend ρ 9 z) (liftPort a) = Port.value ρ a := by
  cases a with
  | zero => rfl
  | var x => exact extend_shift ρ 9 z x 0

@[simp] theorem value_aux {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (z : Fin 9 → Nat) (i : Fin 9) :
    Port.value (extend ρ 9 z) (aux i) = z i :=
  extend_fresh ρ 9 z i

theorem sharedInputs : Targets.SharedInputs := by
  intro Γ ρ z
  exact ⟨fun τ x j => extend_shift ρ 9 z x j,fun i => extend_fresh ρ 9 z i⟩

theorem primitiveRealization : Targets.PrimitiveRealization := by
  intro Γ e
  cases e with
  | port a => cases a <;> exact ⟨rfl,by change 1 ≤ 4; decide⟩
  | successor a => cases a <;> exact ⟨rfl,by change 3 ≤ 4; decide⟩
  | erase a b => cases a <;> cases b <;> exact ⟨rfl,by change 4 ≤ 4; decide⟩
  | identityZero => exact ⟨rfl,by change 4 ≤ 4; decide⟩

@[simp] theorem unused_zero_length (Γ : List Ty) : (unused (Γ:=Γ) 0).length = 9 := rfl
@[simp] theorem unused_one_length (Γ : List Ty) : (unused (Γ:=Γ) 1).length = 8 := rfl
@[simp] theorem unused_two_length (Γ : List Ty) : (unused (Γ:=Γ) 2).length = 7 := rfl

@[simp] theorem lower_length {Γ : List Ty} (g : Gate Γ) : (lower g).length = 10 := by
  cases g <;> simp [lower,addEquations]

theorem graph_pair_sum_bound {Γ : List Ty} (es : List (Expr Γ × Expr Γ)) :
    (es.map (fun e => e.1.graph.specs.length + e.2.graph.specs.length)).sum ≤ 8*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have ha := (primitiveRealization Γ e.1).2
      have hb := (primitiveRealization Γ e.2).2
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

theorem fixedSize : Targets.FixedSize := by
  intro Γ g
  refine ⟨lower_length g,?_,?_⟩
  · simp [forest]
  · have h := graph_pair_sum_bound (lower g)
    simpa only [forestNodes,forest,List.map_map,Function.comp_def,lower_length] using h
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof
