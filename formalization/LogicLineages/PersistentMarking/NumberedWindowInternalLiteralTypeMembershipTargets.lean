module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)

/-- The original scratch membership program on the literal standard encoding
of a supplied finite list. The candidate remains an arbitrary open term. -/
def literalMembership {α : Type} (codes : List Nat) (candidate : OTerm α) : Formula α :=
  memberGraph (numeral (Encodable.encode codes)) candidate

/-- Actual finite disjunction of candidate-to-numeral equalities. Empty lists
give falsity; duplicate codes remain duplicate disjuncts. -/
def literalChoices {α : Type} : List Nat → OTerm α → Formula α
  | [], _ => ⊥
  | code :: rest, candidate => eqn candidate (numeral code) ⊔ literalChoices rest candidate

/-- Exact internal characterization of the original membership graph at a
literal finite list, for every open candidate and every body/context. -/
def ExactLiteralTypeMembership : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (codes : List Nat) (candidate : OTerm α),
    Nonempty (Derivation body Γ
      (((literalMembership codes candidate).imp (literalChoices codes candidate)) ⊓
       ((literalChoices codes candidate).imp (literalMembership codes candidate))))

/-- Finite numerical acceptance gives an internal guard rule at an open
candidate already known to lie in that literal list. The supplied program is
unchanged; each finite branch uses its own original numeral graph. -/
def ExactFiniteProgramGuardTransfer : Prop :=
  ∀ (p : Program 1) (codes : List Nat),
    (∀ code ∈ codes, evaluate p (code ::ᵥ nil) = 1) →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (candidate : OTerm α),
      Nonempty (Derivation body Γ (literalMembership codes candidate)) →
      Nonempty (Derivation body Γ (unary p (suc z) candidate))

/-- An actual graph on an open member of a literal input list has its result
in the literal output list whenever each finite numerical image does. -/
def ExactFiniteProgramImageTransfer : Prop :=
  ∀ (p : Program 1) (inputs outputs : List Nat),
    (∀ code ∈ inputs, evaluate p (code ::ᵥ nil) ∈ outputs) →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (candidate result : OTerm α),
      Nonempty (Derivation body Γ (literalMembership inputs candidate)) →
      Nonempty (Derivation body Γ (unary p result candidate)) →
      Nonempty (Derivation body Γ (literalMembership outputs result))

/-- The actual all-type checker accepts an arbitrary open member of a literal
list of valid type codes. No new checker replaces the supplied TV. -/
def ExactFiniteActualTypeGuard : Prop :=
  ∀ (TV : Program 1) (codes : List Nat), ActualTypeGuard TV →
    (∀ code ∈ codes, typeBit code = true) →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (candidate : OTerm α),
      Nonempty (Derivation body Γ (literalMembership codes candidate)) →
      Nonempty (Derivation body Γ (unary TV (suc z) candidate))

/-- The original refit guard is derivable at an arbitrary open member of the
literal window-type list when its finite entries are valid and lie in the
grammar list. Membership is explicit; no arbitrary window graph is substituted
for this premise, and the scalar type-checker slot is not changed. -/
def ExactFiniteWindowRefitGuard : Prop :=
  ∀ (s : Settings) (T : Program 1), GrammarTypeInclusion s → TypeGuardCalibrated s T →
    (∀ code ∈ s.window.1, typeBit code = true) →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (candidate : OTerm α),
      Nonempty (Derivation body Γ (literalMembership s.window.1 candidate)) →
      Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) candidate))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
