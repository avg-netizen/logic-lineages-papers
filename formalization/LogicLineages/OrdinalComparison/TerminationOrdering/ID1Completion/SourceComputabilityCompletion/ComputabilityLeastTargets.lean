module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Genuine C of the literal original bottom, at arbitrary symbolic Gamma.
Typing, source/member/fixedness and spine-mark facts are conclusions of its
construction, rather than supplied premises. Only membership of the fixed
source type in the local window and the actual original object graph occur. -/
def ActualConcreteBottomComputable : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (window : Program 1), Path.windowCalibrated n window →
  ∀ (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5),
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  ∀ (tau : Ty), tau ∈ S →
  ∀ (α : Type) (Delta : List (Formula α)) (object gammaCode : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((ComputabilityLeast.bottomGraph object (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gammaCode).imp
      (InternalComputabilityApplication.computable comp tau (numeral context) object)))

/-- Original all-finite-type computability implies the SAME scalar I.
Domain bottom membership is derived from the actual typed function graph;
no bottom oracle, ArithmeticRules/lift premise, semantic accessibility,
shape, N-fixedness or successful-run assumption is added. -/
def ActualConcreteComputabilityLeast : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (window : Program 1), Path.windowCalibrated n window →
  ∀ (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5),
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  ∀ (tau : Ty) (α : Type) (Delta : List (Formula α)) (object : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((InternalComputabilityApplication.computable comp tau (numeral context) object).imp
      (InternalAccessibilityRules.membership false object)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastTargets
