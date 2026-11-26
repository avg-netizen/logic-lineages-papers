module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion OriginalVariableComputability

/-- Literal original variable Objects are non-lambda in the arithmetic
calculus, without typing, decoded shape or runtime-coordinate witnesses. -/
def ActualOriginalVariableObjectNonLambda : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (object : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((OriginalVariableObject.variableObject object).imp
      (OriginalSourceNeutralApplication.nonLambdaObject object)))

/-- The SAME globally selected and leaf-refined final tuple serves every
finite source context and all finite types, including arrows. No new source
predicate, independent Gamma selection or externally supplied C law occurs. -/
def ActualOriginalFinalVariableComputability : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  VariableComputable (GlobalSourcePackage.source r)
    (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityTargets
