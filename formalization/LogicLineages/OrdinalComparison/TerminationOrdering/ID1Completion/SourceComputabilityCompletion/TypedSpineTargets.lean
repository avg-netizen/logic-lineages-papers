module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Genuine original I membership for every typed flagged object, via
INTERNAL strong induction on its actual numeric spine depth. The concrete
SAME source/comp tuple is fixed globally before every K and Gamma. No
ArithmeticRules, lift, semantic measure, shape or accessibility oracle is
supplied as an internal or metatheoretic conclusion premise. -/
def ActualConcreteTypedSpineLeast : Prop :=
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
  ∀ (tau : Ty) (α : Type) (Delta : List (Formula α))
    (x mark depth : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((InternalComputabilityApplication.typed comp tau (numeral context) x ⊓
      TypedSpine.marked x mark depth).imp
      (InternalAccessibilityRules.membership false x)))

/-- Genuine finite-type C, in the SAME original combined-body calculus.
Ground uses the internal depth proof; arrow uses original typed application
totality, actualJ full mark and the codomain type IH. Arguments retain the
original same-Gamma guard. No external Acc theorem is reflected. -/
def ActualConcreteTypedSpineComputable : Prop :=
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
  ∀ (tau : Ty) (α : Type) (Delta : List (Formula α))
    (x mark depth : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((InternalComputabilityApplication.typed comp tau (numeral context) x ⊓
      TypedSpine.marked x mark depth).imp
      (InternalComputabilityApplication.computable comp tau (numeral context) x)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineTargets
