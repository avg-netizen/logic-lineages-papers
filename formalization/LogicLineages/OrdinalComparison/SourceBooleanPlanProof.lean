module
public import LogicLineages.OrdinalComparison.SourceBooleanPlanTargets
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanPlan.Proof
open PrimitiveLowering ExistentialPlan

theorem gatesExact : Targets.GatesExact := by
  intro Γ gs ρ
  induction gs with
  | nil => simp [gates,Eval]
  | cons g gs ih =>
      change (g.Holds (inputs ρ) ∧ Eval ρ (gates gs)) ↔ _
      rw [ih]
      simp only [List.mem_cons,forall_eq_or_imp]

theorem bindExact : Targets.BindExact := by
  intro Γ n
  induction n with
  | zero =>
      intro q ρ
      constructor
      · intro h; exact ⟨Fin.elim0,h⟩
      · rintro ⟨v,h⟩; exact h
  | succ n ih =>
      intro q ρ
      change Eval ρ (bindBlock n (.existsGround q)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨v,x,h⟩
        refine ⟨Fin.cons x v,?_⟩
        change Eval (ExistentialPlan.extend (block ρ n v) x) q
        exact h
      · rintro ⟨v,h⟩
        exact ⟨(fun i => v i.succ),v 0,h⟩

theorem block_eq {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (v : Fin n → Nat) :
    block ρ n v = ExistentialPlan.Proof.block ρ n v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [block,ExistentialPlan.Proof.block,ih]

theorem inputs_block {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (v : Fin n → Nat) :
    inputs (block ρ n v) = PrimitiveLowering.extend (inputs ρ) n v := by
  rw [block_eq]
  exact ExistentialPlan.Proof.inputs_block ρ n v

theorem matrixExact : Targets.MatrixExact := by
  intro Γ n m d a root ρ
  unfold matrixPlan
  rw [bindExact]
  apply Iff.trans ?_ (BooleanGlobalFlatten.Proof.existentialExact Γ n m d a root (inputs ρ))
  constructor
  · rintro ⟨v,h⟩
    refine ⟨v,?_⟩
    have hh := (gatesExact _ _ _).mp h
    simpa only [inputs_block,BooleanFlatten.Holds] using hh
  · rintro ⟨v,h⟩
    refine ⟨v,(gatesExact _ _ _).mpr ?_⟩
    simpa only [inputs_block,BooleanFlatten.Holds] using h

theorem gates_vertices {Γ} (gs : List (Gate Γ)) : (gates gs).vertices = 80*gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change 80+(gates gs).vertices = 80*(gs.length+1)
      rw [ih]
      omega

theorem gates_equations {Γ} (gs : List (Gate Γ)) : (gates gs).equations = 10*gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change 10+(gates gs).equations = 10*(gs.length+1)
      rw [ih]
      omega

theorem gates_witnesses {Γ} (gs : List (Gate Γ)) : (gates gs).witnesses = 9*gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change 9+(gates gs).witnesses = 9*(gs.length+1)
      rw [ih]
      omega

theorem bind_vertices {Γ} (n : Nat) (q : Plan (List.replicate n Ty.ground++Γ)) :
    (bindBlock n q).vertices = q.vertices := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.existsGround q)

theorem bind_equations {Γ} (n : Nat) (q : Plan (List.replicate n Ty.ground++Γ)) :
    (bindBlock n q).equations = q.equations := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.existsGround q)

theorem bind_witnesses {Γ} (n : Nat) (q : Plan (List.replicate n Ty.ground++Γ)) :
    (bindBlock n q).witnesses = n+q.witnesses := by
  induction n with
  | zero => exact (Nat.zero_add q.witnesses).symm
  | succ n ih =>
      change (bindBlock n (.existsGround q)).witnesses = n+1+q.witnesses
      rw [ih]
      change n+(1+q.witnesses) = n+1+q.witnesses
      omega

theorem linearOverhead : Targets.LinearOverhead := by
  intro Γ n m d a root
  obtain ⟨hl,hb,_⟩ := BooleanGlobalFlatten.Proof.linearOverhead Γ n m d a root
  simp only [matrixPlan,bind_vertices,bind_equations,bind_witnesses,
    gates_vertices,gates_equations,gates_witnesses]
  rw [hl]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩ <;> omega
end LogicLineages.OrdinalComparison.Source.BooleanPlan.Proof
