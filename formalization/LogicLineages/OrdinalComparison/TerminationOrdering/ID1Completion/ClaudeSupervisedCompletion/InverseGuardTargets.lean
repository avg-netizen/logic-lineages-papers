module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ClaudeSupervisedCompletion.InverseGuardTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalParameterizedApplicationStepChecker
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Independent source-shaped comparison: recovered original constructor
facts, literal child edge and actual original transition, with no calibration
or typing oracle. These are conclusions, not input assumptions. -/
def Recovered {alpha : Type} (endpoint : Program 6)
    (d e arrow f g a k child state S T K parameter : OTerm alpha) : Formula alpha :=
  liftedCheckerPremises endpoint d e arrow f g a k S T K parameter ⊓
    (graph3 edgeCode child f g k ⊓ transitionGraph endpoint child state parameter)

def Unpeeled {alpha : Type} (endpoint : Program 6) (oldChecker : Program 4)
    (out state S T K parameter : OTerm alpha) : Formula alpha :=
  graph2 (guardP endpoint) OrdinaryArithmetic.zeroTerm state parameter ⊓
    (normalizerGraph endpoint state state parameter ⊓ graph4 oldChecker out S T K parameter)

def Peeled {alpha : Type} (endpoint : Program 6) (oldChecker : Program 4)
    (d e arrow f g a k child out state S T K parameter : OTerm alpha) : Formula alpha :=
  graph2 (guardP endpoint) (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) state parameter ⊓
    (Recovered endpoint d e arrow f g a k child state S T K parameter ⊓
      checkerGraph endpoint oldChecker out f g k parameter)

/-- Internal existential/continuation elimination of the actual accepted
original guard. No selected witness or native-evaluation premise is an input. -/
def ActualAcceptedGuardElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 6) (alpha : Type)
    (Gamma : List (Formula alpha)) (state S T K parameter : OTerm alpha)
    (psi : Formula alpha),
  Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)) →
  Nonempty (Derivation body Gamma (graph2 (guardP endpoint) (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) state parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
    ∀ d e arrow f g a k child : OTerm beta,
    Nonempty (Derivation body Delta (Recovered endpoint d e arrow f g a k child
      (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

/-- The source's bounded raw-checker split retains its unchanged leaf. It is
not a neutral quotient/arrow-C or whole context-uniform accessibility theorem. -/
def ActualSelectedCheckerElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 6) (oldChecker : Program 4)
    (alpha : Type) (Gamma : List (Formula alpha))
    (out state S T K parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)) →
  Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out S T K parameter)) →
  Nonempty (Derivation body
    (Unpeeled endpoint oldChecker out state S T K parameter :: Gamma) psi) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
    ∀ d e arrow f g a k child : OTerm beta,
    Nonempty (Derivation body Delta (Peeled endpoint oldChecker d e arrow f g a k child
      (out.relabel j) (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j)
      (parameter.relabel j))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ClaudeSupervisedCompletion.InverseGuardTargets
