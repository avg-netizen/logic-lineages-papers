module
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Targets
open SourcePlanSpineCode SourcePrimitiveForestCode ExistentialPlan PrimitiveLowering

def ExactNumericRecursion : Prop :=
  (∀ a out is,build 0 a out is=(1,a,out,0)::is) ∧
  (∀ e a out is,build (e+1) a out is=(4,0,0,0)::
    build e (shiftPort 1 a) 1 ((2,1,1,shiftPort 1 out)::SourcePlanInsertionCode.insert 0 1 is))

def ExactScaling : Prop := ∀ {Γ} (e : Nat) (a out : Port Γ) (q : Plan Γ),
  ParametricExistentialPlan.Supported q →
  build e (portNumber a) (portNumber out) (spine q)=spine (ParametricScalingPlan.scalePlan e a out q)

def UniformPrimitiveRecursive : Prop := Primrec advance ∧
  Primrec (fun p : Nat×Nat×Nat×List Instruction => build p.1 p.2.1 p.2.2.1 p.2.2.2)
end LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Targets
