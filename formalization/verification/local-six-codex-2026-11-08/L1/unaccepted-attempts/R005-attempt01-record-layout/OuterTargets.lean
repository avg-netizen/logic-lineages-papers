module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Concrete construction law for ONE globally chosen source/comp/lift
family. The unchanged UNQUALIFIED CertifiedApplicationLift and actual
downward derivations are CONCLUSIONS, never assumptions. No Gamma/fiber,
source/target shape, N-fixedness, output type or local compatibility field is
added to their original antecedents. Arbitrary global fallback/multiset/direct
inputs leave the later calibrated existential witness selection open.

This internal endpoint does not assert numerical calibration of arbitrary
fallback inputs; the original all-input source/comp/lift selection remains
a separate native obligation. -/
def ActualConcreteUniformCertificateDownwardPackage : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (window : Program 1), Path.windowCalibrated n window →
  ∀ (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4) (oldVertex oldResult : Program 5),
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let lift := OuterSelection.lift base window oldVertex
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  ArithmeticRules src comp context ∧
    (CertifiedApplicationLift src comp lift context ∧
      ((∀ (α : Type) (tau : Ty) (x : OTerm α),
        Nonempty (Derivation (SourcePresentation.sourceBody src context) []
          ((typed comp tau (numeral context) x).imp (carrier src false context x)))) ∧
        (SourceComputabilityCompletion.InverseApplication.DomainCarrier src comp context ∧
          (SourceComputabilityCompletion.InverseApplication.DomainForward src comp context ∧
            ∀ (tau : Ty) (α : Type) (f g : OTerm α),
            Nonempty (Derivation (SourcePresentation.sourceBody src context) []
              ((computable comp tau (numeral context) f ⊓ edge src false context f g).imp
                (computable comp tau (numeral context) g)))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
