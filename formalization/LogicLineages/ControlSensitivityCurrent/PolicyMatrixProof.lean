module
public import LogicLineages.ControlSensitivityCurrent.PolicyMatrixTargets
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyMatrix
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering ExistentialPlan BooleanPlan

theorem gatesExact : PolicyMatrixTargets.Gates := by
  intro p f Γ gs ρ
  induction gs with
  | nil => simp [gates,PolicyPlan.Eval]
  | cons g gs ih =>
      change (g.Holds (inputs ρ) ∧ PolicyPlan.Eval p f ρ (gates gs)) ↔ _
      rw [ih]
      simp only [List.mem_cons,forall_eq_or_imp]

theorem bindExact : PolicyMatrixTargets.Bind := by
  intro p f Γ n
  induction n with
  | zero =>
      intro q ρ
      constructor
      · intro h; exact ⟨Fin.elim0,h⟩
      · rintro ⟨v,h⟩; exact h
  | succ n ih =>
      intro q ρ
      change PolicyPlan.Eval p f ρ (bindBlock n (.existsGround q)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨v,x,h⟩
        refine ⟨Fin.cons x v,?_⟩
        change PolicyPlan.Eval p f (ExistentialPlan.extend (block ρ n v) x) q
        exact h
      · rintro ⟨v,h⟩
        exact ⟨(fun i => v i.succ),v 0,h⟩

theorem inputs_block {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (v : Fin n → Nat) :
    inputs (block ρ n v) = PrimitiveLowering.extend (inputs ρ) n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext c
      rcases c with ⟨σ,x,j⟩
      cases x with
      | here => rfl
      | there x =>
          have hh := congrFun (ih (fun i => v i.succ)) ⟨σ,x,j⟩
          cases σ <;> exact hh

theorem matrixExact : PolicyMatrixTargets.Matrix := by
  intro p f Γ n m d a root ρ
  unfold matrixPlan
  rw [bindExact p f]
  apply Iff.trans ?_ (BooleanGlobalFlatten.Proof.existentialExact Γ n m d a root (inputs ρ))
  constructor
  · rintro ⟨v,h⟩
    refine ⟨v,?_⟩
    have hh := (gatesExact p f _ _ _).mp h
    simpa only [inputs_block,BooleanFlatten.Holds] using hh
  · rintro ⟨v,h⟩
    refine ⟨v,(gatesExact p f _ _ _).mpr ?_⟩
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

theorem linearOverhead : PolicyMatrixTargets.ActualSize := by
  intro Γ n m d a root
  obtain ⟨hl,hb,_⟩ := BooleanGlobalFlatten.Proof.linearOverhead Γ n m d a root
  simp only [matrixPlan,bind_vertices,bind_equations,bind_witnesses,
    gates_vertices,gates_equations,gates_witnesses]
  rw [hl]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩ <;> omega
end LogicLineages.ControlSensitivityCurrent.PolicyMatrix
