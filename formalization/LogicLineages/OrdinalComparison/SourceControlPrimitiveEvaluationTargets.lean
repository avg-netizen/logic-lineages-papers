module
public import LogicLineages.OrdinalComparison.SourceControlPrimitiveEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceControlPrimitiveEvaluation.Targets

def FixedPrimitiveEvaluation : Prop := ParametricRestrictedSourcePrimitive.Targets.FixedGammaPrimitive

def TypedExactEvaluation : Prop := ∀ (b : Nat) (Γ : List Ty)
    (t : OriginalTerm Γ .ground) (xs : List Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  xs.length=Γ.length →
  (∃ r : Nat, ParametricRestrictedSourceEvaluator.gammaEvaluate b Γ.length
    (SyntaxCode.encodeTerm t) xs=some r) ∧
  (∀ r : Nat, ParametricRestrictedSourceEvaluator.gammaEvaluate b Γ.length
    (SyntaxCode.encodeTerm t) xs=some r ↔
    ParametricSourceEraser.Scalar (SourceMachineControlNonperiodicity.gamma b)
      (fun c => (SourceGroundComponentEnvironment.rawValuation xs c : Ordinal)) t r)

def ExactFiniteIteration : Prop := ∀ b a c : Nat,
  ParametricFinitePairCollapse.value (SourceMachineControlNonperiodicity.gamma b) (a,c)=
    ((SourceMachineControlNonperiodicity.gamma b)^[a]) (2*a+c)+a
end LogicLineages.OrdinalComparison.Source.SourceControlPrimitiveEvaluation.Targets
