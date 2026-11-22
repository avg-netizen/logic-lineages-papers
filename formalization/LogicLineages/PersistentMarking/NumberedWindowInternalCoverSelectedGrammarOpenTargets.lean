module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeReport)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport selectedStep termsPart argsPart termProjection argsProjection)
open NumberedWindowInternalCoverSelectedGrammarTargets

abbrev rowTape {α : Type} (d prev H K M : OTerm α) : Fin 5 → OTerm α := ![d,prev,H,K,M]

/-- The actual chosen zero stage resolves the two original observed
scratch outputs. The argument list also has the actual zero-headed
standard scratch singleton graph, not a sparse argument-cell graph. -/
def ExactOpenSelectedGrammarBaseSplit : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (state terms args H K M : OTerm α),
  Nonempty (Derivation body Γ (grammarReport state z H K M)) →
  Nonempty (Derivation body Γ (termProjection terms state)) →
  Nonempty (Derivation body Γ (argsProjection args state)) →
  Nonempty (Derivation body Γ (eqn z terms ⊓ (eqn (suc z) args ⊓ consGraph args z z)))

/-- One exact literal selected recursion transition on the same H,K,M.
Prerequisites are actual predecessor and successor states, actual prior
pair reads, and the actual range report at the true exclusive bound M+1. -/
def ExactOpenSelectedGrammarSuccessorRow : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (prev next d H K M ids terms args : OTerm α),
  Nonempty (Derivation body Γ (grammarReport prev d H K M)) →
  Nonempty (Derivation body Γ (grammarReport next (suc d) H K M)) →
  Nonempty (Derivation body Γ (termProjection terms prev)) →
  Nonempty (Derivation body Γ (argsProjection args prev)) →
  Nonempty (Derivation body Γ (rangeReport ids (suc M))) →
  Nonempty (Derivation body Γ (stepReport selectedStep next H K ids terms args))

/-- Split the same actual selected successor report at the two observed
next pair projections. No membership or stage transport is asserted. -/
def ExactOpenSelectedGrammarSuccessorSplit : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (prev next d H K M ids terms args nextTerms nextArgs : OTerm α),
  Nonempty (Derivation body Γ (grammarReport prev d H K M)) →
  Nonempty (Derivation body Γ (grammarReport next (suc d) H K M)) →
  Nonempty (Derivation body Γ (termProjection terms prev)) →
  Nonempty (Derivation body Γ (argsProjection args prev)) →
  Nonempty (Derivation body Γ (rangeReport ids (suc M))) →
  Nonempty (Derivation body Γ (termProjection nextTerms next)) →
  Nonempty (Derivation body Γ (argsProjection nextArgs next)) →
  Nonempty (Derivation body Γ
    (stepReport selectedStep next H K ids terms args ⊓
     (stepReport termsPart nextTerms H K ids terms args ⊓ stepReport argsPart nextArgs H K ids terms args)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
