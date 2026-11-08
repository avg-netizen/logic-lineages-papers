module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelection
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Four literal binary leaves, with no correctness, fixed-point, or lift
field. The same tuple is selected before any finite window or ambient Gamma. -/
structure Data where
  oldSource : Program 2
  oldTarget : Program 2
  oldRepresentative : Program 2
  member : Program 2

def Calibrated (n : Nat) (arity : Fin n → Nat) (data : Data) : Prop :=
  InternalOriginalUniformParameterLeaves.Calibrated n arity
    data.oldSource data.oldTarget data.oldRepresentative data.member

/-- Source is the exact conjunction of the two previously checked result
validators. Both children and every membership test retain the same parameter. -/
def validity (data : Data) : Program 2 :=
  InternalParameterizedApplicationValidityFold.sourceP data.oldSource data.oldTarget data.member

def targetValidity (data : Data) : Program 2 :=
  InternalParameterizedApplicationValidityFold.targetP data.oldTarget

/-- Exact-one source validity selects the actual value-bounded descent.
Every other source output retains the original packed-target representative,
including decoded terms outside the source universe. -/
def fallbackRepresentative (representative valid : Program 2) : Program 2 :=
  InternalAcceptance.branch (InternalApplicationValidityStack.exactOne valid)
    representative (InternalParameterizedBoundedDescentNormalizer.normalizer representative valid)

def representative (data : Data) : Program 2 :=
  fallbackRepresentative data.oldRepresentative (validity data)

/-- Inputs are [value,requestedType,parameter]. -/
def validAt (valid : Program 2) : Program 3 :=
  .composition valid ![.projection 0,.projection 2]

def membershipAt (member : Program 2) : Program 3 :=
  .composition member ![.projection 1,.projection 2]

def sameOuterType : Program 3 :=
  InternalApplicationStepPeel.same
    (leftOf (.projection 0)) (.projection 1)

/-- Fixedness is T(value,parameter)=value for the actual binary transition.
It is not a leaf, normalizer or result-fold fixedness assumption. -/
def transitionFixed (representative valid : Program 2) : Program 3 :=
  InternalApplicationStepPeel.same
    (.composition (InternalParameterizedBoundedDescentNormalizer.transition representative valid)
      ![.projection 0,.projection 2]) (.projection 0)

def typedChecker (representative valid member : Program 2) : Program 3 :=
  InternalAcceptance.conjunction (membershipAt member)
    (InternalAcceptance.conjunction (validAt valid)
      (InternalAcceptance.conjunction sameOuterType (transitionFixed representative valid)))

def selectedTyped (data : Data) : Program 3 :=
  typedChecker data.oldRepresentative (validity data) data.member

def representativeGraph {α : Type} (representative valid : Program 2)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (fallbackRepresentative representative valid) out input parameter

def typedAccepted {α : Type} (representative valid member : Program 2)
    (value typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (typedChecker representative valid member) InternalOriginalStepGuard.one value typ parameter

def outputInvariant {α : Type} (representative valid : Program 2)
    (out typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalParameterizedBoundedDescentNormalizer.validGraph valid out parameter ⊓
    (InternalParameterizedBoundedDescentNormalizer.leftGraph typ out ⊓
      InternalParameterizedBoundedDescentNormalizer.transitionGraph representative valid out out parameter)

def typedFactors {α : Type} (representative valid member : Program 2)
    (value typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 member InternalOriginalStepGuard.one typ parameter ⊓
    outputInvariant representative valid value typ parameter

def outputPremises {α : Type} (representative valid : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  representativeGraph representative valid out input parameter ⊓
    (InternalParameterizedBoundedDescentNormalizer.validGraph valid input parameter ⊓
      InternalParameterizedBoundedDescentNormalizer.leftGraph typ input)

def typedOutputPremises {α : Type} (representative valid member : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  outputPremises representative valid out input typ parameter ⊓
    graph2 member InternalOriginalStepGuard.one typ parameter

/-- Source application closure keeps the exact original constructors and
member(codomain,parameter), with no child run-success or semantic premise. -/
def applicationPremises {α : Type} (data : Data)
    (arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph2 data.member InternalOriginalStepGuard.one e parameter ⊓
      (graph2 (validity data) InternalOriginalStepGuard.one fn parameter ⊓
        graph2 (validity data) InternalOriginalStepGuard.one arg parameter))

/-- All natural packed inputs and all requested type codes at the original
paired context/Gamma parameter. No successful-decoding premise is supplied. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  let parameter := InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table
  (∀ value : Nat,
    evaluate (targetValidity data) (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value ∧
    evaluate (validity data) (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value ∧
    evaluate (representative data) (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value) ∧
  (∀ value typ : Nat,
    evaluate (selectedTyped data) (List.Vector.ofFn ![value,typ,parameter]) =
      InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma (List.Vector.ofFn ![value,typ]))

/-- Properties to PROVE about the same selected ASTs. No proof is a Data
field, and every parameter remains symbolic in every internal derivation. -/
def InternalLaws (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
  (∀ value parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Delta
      ((graph2 (validity data) InternalOriginalStepGuard.one value parameter).imp
        (graph2 (targetValidity data) InternalOriginalStepGuard.one value parameter)))) ∧
  (∀ value typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Delta
      ((typedAccepted data.oldRepresentative (validity data) data.member value typ parameter).iff
        (typedFactors data.oldRepresentative (validity data) data.member value typ parameter)))) ∧
  (∀ out input typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Delta
      ((outputPremises data.oldRepresentative (validity data) out input typ parameter).imp
        (outputInvariant data.oldRepresentative (validity data) out typ parameter)))) ∧
  (∀ out input typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Delta
      ((typedOutputPremises data.oldRepresentative (validity data) data.member out input typ parameter).imp
        (typedAccepted data.oldRepresentative (validity data) data.member out typ parameter)))) ∧
  (∀ arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Delta
      ((applicationPremises data arrow d e fp ap fn arg parent parameter).imp
        (graph2 (validity data) InternalOriginalStepGuard.one parent parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelection
