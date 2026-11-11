module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffix
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- At a nonzero ORIGINAL path code, the ordinary and positive checker have
identical cons behavior. This contract changes neither the code nor any edge
certificate. It is independent of source guards and Object reconstruction. -/
def NonzeroPathPositive (edge : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (x y code parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    (((equal code OrdinaryArithmetic.zeroTerm).not ⊓
      InternalParameterizedPathChecker.pathGraph edge x y code parameter).imp
      (InternalParameterizedPathChecker.positiveGraph edge x y code parameter)))

/-- The original active window and same typed endpoints of a literal positive
path. No guard, mark, decoded list or additional certificate is supplied. -/
def positivePremises {alpha : Type} (data : Data) (window : Program 1)
    (oldStep : Program 4) (x y code typ parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window x parameter ⊓
    (typedAccepted data x typ parameter ⊓
      (typedAccepted data y typ parameter ⊓
        InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
          x y code parameter))

/-- Add both literal original guards to a positive path at the SAME code.
The source bottom test and entire flag/depth measure are the unchanged
concrete observers, not externally supplied invariants. -/
def PositivePathGuards (data : Data) (window : Program 1) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (x y code typ parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((positivePremises data window oldStep x y code typ parameter).imp
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker data oldStep) x y code parameter)))

/-- Both Objects are paired at the SAME runtime Gamma. The original parameter
is paired from that Gamma and the source context, and the same original
ordinary checker retains the supplied suffix code literally. -/
def objectPremises {alpha : Type} (data : Data) (window : Program 1)
    (oldStep : Program 4) (context : Nat)
    (source target gammaCode x y code typ parameter : OTerm alpha) : Formula alpha :=
  graph1 window InternalOriginalStepGuard.one (numeral context) ⊓
    (graph2 InternalPairing.pairing parameter (numeral context) gammaCode ⊓
      (graph2 InternalPairing.pairing source gammaCode x ⊓
        (graph2 InternalPairing.pairing target gammaCode y ⊓
          (typedAccepted data x typ parameter ⊓
            (typedAccepted data y typ parameter ⊓
              InternalParameterizedPathChecker.pathGraph (edgeChecker data oldStep)
                x y code parameter)))))

/-- Nil yields literal Object equality. A nonempty suffix supplies the actual
original guarded source certificate with that SAME code. No new list is
constructed, and no application shape is imposed on the final endpoint. -/
def objectConclusion {alpha : Type} (src : SourcePresentation.Data) (context : Nat)
    (source target code : OTerm alpha) : Formula alpha :=
  (equal code OrdinaryArithmetic.zeroTerm ⊓ equal source target) ⊔
    ((equal code OrdinaryArithmetic.zeroTerm).not ⊓
      InternalAccessibilityRules.certificate src false context source target code)

def ObjectSuffix (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (source target gammaCode x y code typ parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((objectPremises data window oldStep context source target gammaCode x y code typ parameter).imp
      (objectConclusion src context source target code)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffix
