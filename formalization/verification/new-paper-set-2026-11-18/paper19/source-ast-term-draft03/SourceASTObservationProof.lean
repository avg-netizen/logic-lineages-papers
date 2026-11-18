module
public import LogicLineages.ControlSensitivityCurrent.SourceASTTermTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
public import LogicLineages.OrdinalComparison.SourceStructural
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence

theorem sourceValue_rename (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ Δ}
    (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (t : Input Γ .ground) :
    InputNormalization.sourceValue p f ν (ScopedDAG.renameInput r t) =
      InputNormalization.sourceValue p f ρ t := by
  unfold InputNormalization.sourceValue
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r t).1]
  have hc : ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      ExistentialPlan.inputs ν ⟨τ,r x,j⟩=ExistentialPlan.inputs ρ ⟨τ,x,j⟩ := by
    intro τ x j
    cases τ with
    | ground => exact h x
    | arrow a b => rfl
  rw [PolicyObservation.sourceNaturality p f Γ Δ r _ _ hc t.term]

theorem call_term {Γ} (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground) :
    (BooleanCompiler.call h x).term = .app (h.term.rename (BooleanCompiler.emptyRename Γ)) (.var x) := by
  unfold BooleanCompiler.call
  rw [(ScopedDAG.Proof.application Γ .ground .ground _ _).1,
    (ScopedDAG.Proof.«renaming» [] Γ (.arrow .ground .ground) (BooleanCompiler.emptyRename Γ) h).1]
  rfl

def singletonRename {Γ} (x : Variable Γ .ground) : Renaming [.ground] Γ
  | _, .here => x
  | _, .there y => nomatch y

theorem call_value (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) (h : Input [] (.arrow .ground .ground))
    (x : Variable Γ .ground) :
    InputNormalization.sourceValue p f ρ (BooleanCompiler.call h x) = callValue p f h (ρ x) := by
  let r : Renaming [.ground] Γ := singletonRename x
  let ν := ExistentialPlan.extend (fun y : Variable [] .ground => nomatch y) (ρ x)
  have hc : ∀ y, ρ (r y)=ν y := by
    intro y
    cases y with
    | here => rfl
    | there y => nomatch y
  have ht : (ScopedDAG.renameInput r (BooleanCompiler.call h (Variable.here : Variable [.ground] .ground))).term =
      (BooleanCompiler.call h x).term := by
    rw [(ScopedDAG.Proof.«renaming» [.ground] Γ .ground r _).1,call_term,call_term]
    simp only [Source.Term.rename,Source.Term.rename_composition]
    have he : (fun {τ} (y : Variable [] τ) => r (BooleanCompiler.emptyRename [.ground] y)) =
        (fun {τ} (y : Variable [] τ) => BooleanCompiler.emptyRename Γ y) := by
      funext τ y
      nomatch y
    rw [he]
    rfl
  have hh := sourceValue_rename p f r ν ρ hc (BooleanCompiler.call h (Variable.here : Variable [.ground] .ground))
  change PolicyCollision.rawScalar p f (ExistentialPlan.inputs ρ) _ - 1 = _ at hh
  rw [ht] at hh
  exact hh
end LogicLineages.ControlSensitivityCurrent.SourceAST
