module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Targets
open PrimitiveLowering ParametricSourceEraser

def ExactExpressionCalibration : Prop := ∀ (G : Nat → Nat), StrictMono G →
  (∀ n : Nat,n ≤ G n) → ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (e : Expr Γ),
  Scalar G (positive ρ) e.term (value G ρ e+1) ∧
  ∀ n : Nat, Scalar G (positive ρ) e.term n ↔ n=value G ρ e+1

def FullComponentRenaming : Prop := ∀ (G : Nat → Nat) (Γ Δ : List Ty)
    (r : Renaming Γ Δ) (ρ : OrdinalComponent Γ → Nat) (ν : OrdinalComponent Δ → Nat),
  (∀ c,ν (ordinalComponentRename r c)=ρ c) →
  ∀ (t : OriginalTerm Γ .ground) (n : Nat),
    Scalar G (positive ν) (t.rename r) n ↔ Scalar G (positive ρ) t n

def GroundInputDAGRenaming : Prop := ∀ (G : Nat → Nat) (Γ Δ : List Ty)
    (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
  (∀ x,ν (r x)=ρ x) → ∀ (t : GroundEquivalence.Input Γ .ground) (n : Nat),
    Scalar G (positive (ExistentialPlan.inputs ν)) (ScopedDAG.renameInput r t).term n ↔
      Scalar G (positive (ExistentialPlan.inputs ρ)) t.term n

def ActualGammaExpressions : Prop := ∀ (b : Nat) (Γ : List Ty)
    (ρ : OrdinalComponent Γ → Nat) (e : Expr Γ),
  Scalar (SourceMachineControlNonperiodicity.gamma b) (positive ρ) e.term
    (value (SourceMachineControlNonperiodicity.gamma b) ρ e+1) ∧
  ∀ n : Nat, Scalar (SourceMachineControlNonperiodicity.gamma b) (positive ρ) e.term n ↔
    n=value (SourceMachineControlNonperiodicity.gamma b) ρ e+1
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Targets
