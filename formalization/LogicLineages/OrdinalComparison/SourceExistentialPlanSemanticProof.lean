module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
public import LogicLineages.OrdinalComparison.SourceUnitEliminationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
open OriginalDomain GroundEquivalence PrimitiveLowering
open SourceCollisionCompletion SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem valuation_inputs {Γ} (ρ : Variable Γ .ground → Nat) :
    valuation (UnitObservation.substitution ρ)=(fun c => ((inputs ρ c+1 : Nat) : Ordinal)) :=
  UnitElimination.Proof.valuation_inputs ρ

theorem valuation_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) :
    (fun c => valuation (UnitObservation.substitution ν) (ordinalComponentRename r c))=
      valuation (UnitObservation.substitution ρ) := by
  rw [valuation_inputs,valuation_inputs]
  funext c
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground => exact congrArg (fun n : Nat => ((n+1 : Nat) : Ordinal)) (h x)
  | arrow a b => rfl

theorem raw_rename {Γ Δ} (r : Renaming Γ Δ) (t : OriginalTerm Γ .ground)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) :
    rawScalar (valuation (UnitObservation.substitution ν)) (t.rename r)=
      rawScalar (valuation (UnitObservation.substitution ρ)) t := by
  obtain ⟨v,hv,hs⟩ := actualScalarTotal Γ t
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r)=
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ .ground r OrdinalSyntax.defaultPolicy t,hv]
    rfl
  apply raw_of_assignment _ _ _ _ hr
  change denote (valuation (UnitObservation.substitution ν)) (ordinalExpressionRename r (v 0))=_
  rw [AbsoluteObserver.Proof.rename_value,valuation_rename r ρ ν h]
  exact (hs (UnitObservation.substitution ρ)).1

theorem equation_raw {Γ} (ρ : Variable Γ .ground → Nat) (a b : OriginalTerm Γ .ground) :
    SourceAdditionCompletion.Equation (inputs ρ) a b ↔
      rawScalar (valuation (UnitObservation.substitution ρ)) a=
        rawScalar (valuation (UnitObservation.substitution ρ)) b := by
  obtain ⟨va,ha,hsa⟩ := actualScalarTotal Γ a
  obtain ⟨vb,hb,hsb⟩ := actualScalarTotal Γ b
  constructor
  · rintro ⟨wa,wb,hwa,hwb,he⟩
    rw [ha] at hwa
    rw [hb] at hwb
    cases Option.some.inj hwa
    cases Option.some.inj hwb
    rw [← valuation_inputs,(hsa (UnitObservation.substitution ρ)).1,(hsb (UnitObservation.substitution ρ)).1] at he
    exact Nat.cast_injective he
  · intro he
    refine ⟨va,vb,ha,hb,?_⟩
    rw [← valuation_inputs,(hsa (UnitObservation.substitution ρ)).1,(hsb (UnitObservation.substitution ρ)).1,he]

theorem equation_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (a b : OriginalTerm Γ .ground) :
    SourceAdditionCompletion.Equation (inputs ν) (a.rename r) (b.rename r) ↔
      SourceAdditionCompletion.Equation (inputs ρ) a b := by
  rw [equation_raw,equation_raw,raw_rename r a ρ ν h,raw_rename r b ρ ν h]

theorem equation_dag_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (a b : Input Γ .ground) :
    SourceAdditionCompletion.Equation (inputs ν) (ScopedDAG.renameInput r a).term (ScopedDAG.renameInput r b).term ↔
      SourceAdditionCompletion.Equation (inputs ρ) a.term b.term := by
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r a).1,(ScopedDAG.Proof.«renaming» Γ Δ .ground r b).1]
  exact equation_rename r ρ ν h a.term b.term

theorem port_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (a : Port Γ) :
    (portRename r a).value (inputs ν)=a.value (inputs ρ) := by
  cases a with
  | zero => rfl
  | var x => exact h x

theorem gate_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (g : Gate Γ) :
    (gateRename r g).Holds (inputs ν) ↔ g.Holds (inputs ρ) := by
  cases g <;> simp only [gateRename,Gate.Holds,port_rename r ρ ν h]

def block {Γ} (ρ : Variable Γ .ground → Nat) :
    (n : Nat) → (Fin n → Nat) → Variable (List.replicate n Ty.ground++Γ) .ground → Nat
  | 0, _ => ρ
  | n+1, z => extend (block ρ n (fun i => z i.succ)) (z 0)

theorem inputs_block {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat) :
    inputs (block ρ n z)=PrimitiveLowering.extend (inputs ρ) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext c
    rcases c with ⟨σ,x,j⟩
    cases x with
    | here => rfl
    | there x =>
      have hh := congrFun (ih (fun i => z i.succ)) ⟨σ,x,j⟩
      cases σ <;> exact hh

theorem block_shift {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat)
    (x : Variable Γ .ground) : block ρ n z (shift n x)=ρ x := by
  have hh := PrimitiveLowering.Proof.extend_shift (inputs ρ) n z x 0
  rw [← inputs_block] at hh
  exact hh

theorem block_fresh {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat)
    (i : Fin n) : block ρ n z (fresh i)=z i := by
  have hh := PrimitiveLowering.Proof.extend_fresh (inputs ρ) n z i
  rw [← inputs_block] at hh
  exact hh

theorem block_decompose {Γ} (n : Nat) (ν : Variable (List.replicate n Ty.ground++Γ) .ground → Nat) :
    block (fun x => ν (shift n x)) n (fun i => ν (fresh i))=ν := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    cases x with
    | here => rfl
    | there x => exact congrFun (ih (fun x => ν (.there x))) x
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
