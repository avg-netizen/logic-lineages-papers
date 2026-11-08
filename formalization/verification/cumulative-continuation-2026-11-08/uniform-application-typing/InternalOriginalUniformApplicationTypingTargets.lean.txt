module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalOriginalUniformApplicationTyping

/-- Exact zero-or-one membership output at every symbolic Gamma code. Only
the context and original source type are closed numerals. Global calibration
is used for that closed computation; no symbolic semantic reflection occurs.
Subtype closure and successful Gamma decoding are not premises. -/
def ActualOriginalUniformNormalizedMembershipNumeral : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool) (tau : Ty)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (parameter gammaCode : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table)
      parameter gammaCode).imp
      (memberGraph (normalizeData data) (numeral ((decide (tau ∈ S)).toNat))
        (numeral (typeNumber tau)) parameter)))

/-- Arrow membership is an internal actual graph, not an external premise
that the arrow belongs to S. Subtype closure and the exact closed zero/one
slice suffice to derive codomain membership at the same runtime parameter. -/
def ActualOriginalUniformNormalizedCodomainMembership : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    (((parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table)
      parameter gammaCode) ⊓
      memberGraph (normalizeData data) InternalOriginalStepGuard.one
        (numeral (typeNumber (.arrow sigma tau))) parameter).imp
      (memberGraph (normalizeData data) InternalOriginalStepGuard.one
        (numeral (typeNumber tau)) parameter)))

/-- ActualJ preserves canonical typing for arbitrary Data, symbolic type
codes and parameter. Its supplied function is not normalized again, and no
N(function)=function or N(argument)=argument assumption is supplied. -/
def ActualParameterizedCanonicalApplicationTypedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (arrow domain codomain function argument out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((applicationPremises data arrow domain codomain function argument out parameter).imp
      (typedGraph data out codomain parameter)))

/-- Strengthen EVERY globally calibrated base tuple, preserving the exact
normalization and all previous package conclusions before windows and Gamma.
The new application rule derives codomain membership; it adds no new leaf,
decoder, calibration premise on symbolic terms, or certified-path-lift claim. -/
def ActualOriginalUniformNormalizedApplicationTyping : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  RetainedNormalizedPackage n arity data ∧
    UniformApplicationLaw n (normalizeData data)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingTargets
