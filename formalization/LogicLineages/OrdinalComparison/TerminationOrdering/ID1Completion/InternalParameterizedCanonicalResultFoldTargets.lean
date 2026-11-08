module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedCanonicalResultFold

/-- Actual raw N output plus input V/type yield actual H acceptance, output
V, the same raw type and T-fixedness at the SAME arbitrary parameter. -/
def ActualParameterizedCanonicalFoldOutputInvariant : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Gamma : List (Formula α))
    (out input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises data input typ parameter).imp
      ((foldGraph data out input parameter).imp
        (successfulOutput data out input typ parameter))))

/-- Actual internally bound output, from source validity and its original
type alone. No child-success, canonical-input or calibration hypothesis. -/
def ActualParameterizedCanonicalFoldCertifiedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Gamma : List (Formula α))
    (input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises data input typ parameter).imp
      (hasCertifiedOutput data input typ parameter)))

/-- Requested-type membership is an ACTUAL graph premise of the same
binary leaf. The conclusion uses the frozen ternary canonical typed AST. -/
def ActualParameterizedCanonicalFoldTypedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Gamma : List (Formula α))
    (out input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises data input typ parameter).imp
      ((graph2 data.member InternalOriginalStepGuard.one typ parameter).imp
        ((foldGraph data out input parameter).imp
          (typedOutput data out input typ parameter)))))

/-- Internal representative/application transport for the ORIGINAL raw
parent and actual parameterized J, with codomain membership retained. -/
def ActualParameterizedCanonicalRepresentativeApplicationTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Gamma : List (Formula α))
    (arrow d e fn arg parent x out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((representativePremises data arrow d e fn arg parent x out parameter).imp
      (representativeConclusion data parent out e parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldTargets
