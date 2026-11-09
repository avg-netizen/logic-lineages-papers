module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackage
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only original globally selected Program ASTs. There is no finite window,
ambient Gamma, internal correctness field, source-case oracle or derivation
stored here. The unary window Program reads the caller's original Context. -/
structure Inputs where
  base : Data
  window : Program 1
  oldSrc : SourcePresentation.Data
  oldComp : JointGammaComputability.Data
  oldStep : Program 4
  oldVertex : Program 5
  oldResult : Program 5

/-- Existing native contracts for the original global input Programs only.
The no-premise selection target must prove this conjunction; it is not an
assumed supplier of any final internal law or final source calibration. -/
def InputsCalibrated (n : Nat) (arity : Fin n → Nat) (p : Inputs) : Prop :=
  InternalOriginalUniformDescentSelection.Calibrated n arity p.base ∧
  Path.windowCalibrated n p.window ∧
  ContextUniform.Calibrated p.oldSrc n arity ∧
  JointGammaComputability.Calibrated p.oldComp n arity ∧
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity p.oldStep ∧
  (∀ v : List.Vector Nat 5, evaluate p.oldVertex v = RuntimeVertex.value n arity v) ∧
  (∀ v : List.Vector Nat 5, evaluate p.oldResult v = ApplicationResultBuilder.resultValue n arity v)

/-- These are the SAME accepted OuterSelection constructors. Membership is
normalized once inside their shared Data, never once per native wrapper. -/
abbrev source (p : Inputs) : SourcePresentation.Data :=
  OuterSelection.source p.oldSrc p.oldComp p.base p.oldStep p.window

abbrev computability (p : Inputs) : JointGammaComputability.Data :=
  OuterSelection.computability p.oldComp p.base p.window p.oldVertex p.oldResult

abbrev lift (p : Inputs) : Program 5 :=
  OuterSelection.lift p.base p.window p.oldVertex

abbrev result (p : Inputs) : Program 5 :=
  Outer.result p.oldComp (OuterSelection.data p.base p.window)
    p.window p.oldVertex p.oldResult

/-- The full unchanged R005 internal conjunction at one original Context.
CertifiedApplicationLift and downward closure are CONCLUSIONS, not premises.
All original source formulas, symbolic terms and certificate graphs remain. -/
def WindowPackage (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (pathLift : Program 5) (context : Nat) : Prop :=
  ArithmeticRules src comp context ∧
    (CertifiedApplicationLift src comp pathLift context ∧
      ((∀ (α : Type) (tau : Ty) (x : OTerm α),
        Nonempty (Derivation (SourcePresentation.sourceBody src context) []
          ((typed comp tau (numeral context) x).imp (carrier src false context x)))) ∧
        (SourceComputabilityCompletion.InverseApplication.DomainCarrier src comp context ∧
          (SourceComputabilityCompletion.InverseApplication.DomainForward src comp context ∧
            ∀ (tau : Ty) (α : Type) (f g : OTerm α),
            Nonempty (Derivation (SourcePresentation.sourceBody src context) []
              ((computable comp tau (numeral context) f ⊓ edge src false context f g).imp
                (computable comp tau (numeral context) g)))))))

/-- Complete original native calibration followed by ALL finite source
windows for ONE source/computability/lift triple. Gamma is encoded in the
original Objects, not fixed or added as a selection parameter. This does
not assert the separate closed all-term accessibility formula. -/
def Package (n : Nat) (arity : Fin n → Nat) (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (pathLift : Program 5) : Prop :=
  ContextUniform.Calibrated src n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  (∀ v : List.Vector Nat 5,
    evaluate pathLift v = ApplicationCertificateLiftPath.pathValue n arity v) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    WindowPackage src comp pathLift (OrdinaryArithmeticQuotient.contextCode symbols S table))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackage
