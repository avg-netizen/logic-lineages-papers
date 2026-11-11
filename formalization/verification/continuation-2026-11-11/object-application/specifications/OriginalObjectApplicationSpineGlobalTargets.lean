module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalTargets
open UniformCertificateCompletion OriginalObjectApplicationSpineGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ONE original tuple is selected before all source contexts and Gamma values.
Refine its original leaf once, retaining full-output equality on every raw
input and native calibration; then apply the SAME unchanged finalInputs
pipeline. The entire prior Object/global conjunction and the unconditional
raw-step spine guard hold at that ONE final tuple. Neither a source/Object
positive certificate nor finite-type computability is assumed or asserted. -/
def ActualOriginalObjectApplicationSpineGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let q := OriginalSpineGuardLeaf.refineInputs p
     (∀ v : List.Vector Nat 4, evaluate q.oldStep v = evaluate p.oldStep v) ∧
     GlobalSourcePackage.InputsCalibrated n arity q ∧
     FinalProperties n arity q ∧
     (let r := OriginalApplicationSidecar.finalInputs q
      OriginalSelectedStepSpine.RawStepHasSpineGuard
        (OuterSelection.data r.base r.window) r.oldStep))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalTargets
