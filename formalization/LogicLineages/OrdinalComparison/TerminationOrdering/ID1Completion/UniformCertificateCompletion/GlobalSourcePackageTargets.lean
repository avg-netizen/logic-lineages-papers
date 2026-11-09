module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageTargets
open GlobalSourcePackage
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Joint original global witness selection, after n/arity and BEFORE any
finite symbols/types/table window, Gamma, raw value or symbolic formula.
Every existing native calibration is a conclusion. There is no supplied
primitive-recursiveness, correctness field or separate per-fiber package. -/
def ActualOriginalGlobalInputSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : Inputs, InputsCalibrated n arity p

/-- Exact construction from globally calibrated original inputs. It retains
the literal paired result, FULL original Option success on activation,
including some 0, and the SAME source/computability/path Programs. All-input
native calibration and the entire original R005 internal package are
conclusions. No native-to-internal reflection or correctness oracle is
permitted, and no new path dispatcher or oldLift parameter is introduced. -/
def ActualOriginalGlobalSourcePackageConstruction : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : Inputs),
  InputsCalibrated n arity p →
  (∀ v : List.Vector Nat 5,
    evaluate (result p) v = ApplicationResultBuilder.resultValue n arity v) ∧
  (∀ v : List.Vector Nat 5,
    evaluate (Outer.resultActivation p.oldComp (OuterSelection.data p.base p.window) p.window) v = 1 →
    ApplicationResultBuilder.resultOption n arity v =
      some (evaluate (Outer.resultBranch
        (Path.vertex (OuterSelection.data p.base p.window) p.window p.oldVertex)) v) ∧
    ApplicationResultBuilder.resultOption n arity v = some (evaluate (result p) v) ∧
    ApplicationResultBuilder.successValue n arity v = 1 ∧
    (evaluate (result p) v = 0 → ApplicationResultBuilder.resultOption n arity v = some 0)) ∧
  Package n arity (source p) (computability p) (lift p)

/-- ONE calibrated source, computability and original path transformer
precede EVERY finite source window. The original unqualified certificate
lift, all-type downward derivations and carrier/domain laws are proved,
not hypotheses. This strengthens the old conditional downward reduction
without claiming constructor/multiset/lambda/substitution laws or closed
all-term ID1. Original Object/checker/certificate encodings are unchanged. -/
def ActualOriginalGlobalSourceDownwardPackageExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (pathLift : Program 5),
    Package n arity src comp pathLift

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageTargets
