module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalParameterizedApplicationStepChecker
open OriginalNonapplicationChecker UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output fixed-point law for the ORIGINAL parameterized raw-list
recursor, at every symbolic raw list code, including malformed certificates.
Only this generic theorem has a transition fixed-point antecedent. It is an
object-language graph, not native correctness or an internal reflection rule.
No numeric fuel or replacement list codec is introduced. -/
def ActualOriginalParameterizedRawListFixedPoint : Prop :=
  ∀ (transition : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Delta : List (Formula α)) (out code initial parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 transition initial initial parameter).imp
      ((repeatGraph transition out code initial parameter).iff
        (equal out initial))))

/-- The actual original checker has exactly the old checker's ARBITRARY
output whenever the raw source root is not an application. Source, target,
whole original step certificate and separate parameter are all unchanged.
The original structural guard must discharge transition fixedness internally;
neither a fixed-point hypothesis nor a calibration premise occurs here. -/
def ActualOriginalNonapplicationCheckerCollapse : Prop :=
  ∀ (endpoint : Program 6) (oldChecker : Program 4)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (out source target certificate parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((nonapplicationRoot source).imp
      ((checkerGraph endpoint oldChecker out source target certificate parameter).iff
        (graph4 oldChecker out source target certificate parameter))))

/-- Lift the already-paid literal variable-to-bottom and exact-bottom
rejection laws through the ACTUAL guarded normalized step checker. The same
final refinement is applied once to the globally selected original Inputs.
This universal internal rule introduces no new selection or oracle premise;
it specializes directly to the witness preceding all windows and Gamma in
ActualOriginalVariableRepresentativeGlobalSelection. -/
def ActualOriginalNormalizedConstructorCases : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs),
    let r := OriginalVariableRepresentative.refineInputs p
    OriginalConstructorLeaf.ConstructorCases
      (stepChecker (OuterSelection.data r.base r.window) r.oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerTargets
