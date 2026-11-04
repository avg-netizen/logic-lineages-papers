module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator
noncomputable def evaluate (H : Nat × Nat → Nat) (i n code : Nat) (xs : List Nat) : Option Nat :=
  if xs.length=n ∧ SyntaxCode.check (List.replicate n (SyntaxCode.typeCode Ty.ground)) code=
      some (SyntaxCode.typeCode Ty.ground) then do
    let vector ← DefaultSourceAssignment.assignmentCode (List.replicate n (SyntaxCode.typeCode Ty.ground)) code
    let scalar ← vector[0]?
    pure (ParametricOmegaFreeEvaluator.evaluate H i (SourceGroundComponentEnvironment.environment xs) scalar)
  else none
noncomputable def gammaEvaluate (b n code : Nat) (xs : List Nat) : Option Nat :=
  evaluate (fun p => SourceMachineControlNonperiodicity.gamma b p.2) 0 n code xs
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator
