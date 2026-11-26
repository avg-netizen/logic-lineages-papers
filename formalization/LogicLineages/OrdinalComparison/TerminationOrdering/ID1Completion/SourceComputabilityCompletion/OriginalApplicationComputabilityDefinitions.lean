module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputability
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalComputabilityDownward
open SourceComputabilityFormulaSupportProof (numeral)

/-- An ORIGINAL accepted application at its typed same-Gamma domain is
itself non-lambda. This concerns the actual application output, never a
later positive-path endpoint. The supplied function may itself be a lambda;
no function-neutrality, output-coordinate or raw-application graph is assumed. -/
def AcceptedOutputNonLambda (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (sigma tau : Ty) (function argument out : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((domain comp context sigma tau function argument ⊓
      accepted comp sigma tau (numeral context) function argument out).imp
      (OriginalSourceNeutralApplication.nonLambdaObject out)))

/-- Computability of both ORIGINAL input Objects and their SAME-Gamma guard
make every accepted ORIGINAL output computable. The exact original arrow
formula, application checker and requested output remain unchanged. Neither
activation metadata nor output uniqueness is supplied by the caller. -/
def AcceptedApplicationComputable (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (sigma tau : Ty) (function argument out : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((premises comp sigma tau (numeral context) function argument ⊓
      accepted comp sigma tau (numeral context) function argument out).imp
      (computable comp tau (numeral context) out)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputability
