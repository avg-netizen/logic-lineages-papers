module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Targets
open SourceGroundComponentEnvironment ParametricSourceEraser

def UniformComputable : Prop := ∀ H : Nat × Nat → Nat, Computable H →
  Computable (fun p : (Nat × Nat) × (Nat × List Nat) => evaluate H p.1.1 p.1.2 p.2.1 p.2.2)

def TypedCalibration : Prop := ∀ (H : Nat × Nat → Nat) (i : Nat)
    (Γ : List Ty) (t : OriginalTerm Γ .ground) (xs : List Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  xs.length=Γ.length →
  (∃ r : Nat, evaluate H i Γ.length (SyntaxCode.encodeTerm t) xs=some r) ∧
  (∀ r : Nat, evaluate H i Γ.length (SyntaxCode.encodeTerm t) xs=some r ↔
    Scalar (fun n => H (i,n)) (fun c => (rawValuation xs c : Ordinal)) t r)

def FixedGammaComputable : Prop := ∀ b : Nat,
  Computable (fun p : Nat × (Nat × List Nat) => gammaEvaluate b p.1 p.2.1 p.2.2)

def GeneratedAggregate : Prop := ∀ (b e : Nat) (xs : List Nat),
  xs.length=(ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).context.length →
  ∃ l r : Nat,
    gammaEvaluate b xs.length (SyntaxCode.encodeTerm (SourceMachineAggregateBridge.aggregate b e).1) xs=some l ∧
    gammaEvaluate b xs.length (SyntaxCode.encodeTerm (SourceMachineAggregateBridge.aggregate b e).2) xs=some r ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (rawValuation xs c : Ordinal))
      (SourceMachineAggregateBridge.aggregate b e).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (rawValuation xs c : Ordinal))
      (SourceMachineAggregateBridge.aggregate b e).2 r
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Targets
