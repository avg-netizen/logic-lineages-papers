module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafTargets
open OriginalLambdaGuardLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact total selector equations, including malformed codes. In particular
stripCertificate is the existing stripStep, and the original parameter's left
coordinate and Gamma encoding retain their literal positions. -/
def ActualOriginalLambdaGuardLeafRawCalibration : Prop :=
  (∀ certificate : Nat,
    evaluate stripCertificate (List.Vector.ofFn ![certificate]) =
      OriginalLambdaCertificate.stripStep certificate) ∧
  (∀ v : List.Vector Nat 4,
    let d := (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1
    let e := (Nat.unpair ((Nat.unpair (v.get 0)).1 - 1)).2
    evaluate sourceDomain v = d ∧
      evaluate sourceCodomain v = e ∧
      evaluate sourceBody v =
        Nat.pair e (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2 ∧
      evaluate targetBody v =
        Nat.pair e (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).2 ∧
      evaluate childCertificate v = OriginalLambdaCertificate.stripStep (v.get 2) ∧
      evaluate childParameter v =
        Nat.pair (Nat.unpair (v.get 3)).1
          (Nat.succ (Nat.pair d (Nat.unpair (v.get 3)).2)))

/-- Full-output equality on EVERY original raw input. Only the original
LeafCalibrated premise is allowed. Malformed contexts, failed decodings and
rejected steps are included; no new type-window or child-acceptance premise
is supplied. Successful lambda cases must use the SAME accepted certificate. -/
def ActualOriginalLambdaGuardLeafRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4),
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ v : List.Vector Nat 4, evaluate (refined oldStep) v = evaluate oldStep v

/-- Pure original-AST algebra for arbitrary oldStep, with no native
calibration hypothesis. Acceptance retains the old factor, exposes the
literal guard, and selects the exact matching-target/child-check branch. -/
def ActualOriginalLambdaGuardLeafInternalCases : Prop :=
  ∀ oldStep : Program 4,
    OriginalConstructorLeaf.OriginalFactor oldStep (refined oldStep) ∧
      LeafHasGuard oldStep (refined oldStep) ∧
        LeafHasChildBranch oldStep (refined oldStep)

/-- Internally produce and eliminate the actual body/certificate/parameter
witnesses and recover ORIGINAL old-leaf acceptance. No native-to-internal
reflection principle, supplied child witnesses or new source relation occurs.
This is a leaf supplier only, not global selection or lambda computability. -/
def ActualOriginalLambdaGuardLeafInternalChildElimination : Prop :=
  ∀ oldStep : Program 4, InternalChildElimination oldStep (refined oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafTargets
