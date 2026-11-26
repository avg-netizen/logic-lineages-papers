module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedSuccessorTargets (argsPart stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)

def ExactOpenSelectedNonemptyArgsRow : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args q tail : OTerm α),
    Nonempty (Derivation body Γ (stepReport argsPart out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph terms q)) →
    Nonempty (Derivation body Γ (memberGraph args tail)) →
    Nonempty (Derivation body Γ (memberGraph out (rawCons q tail)))

def ExactOpenSelectedNonemptyArgsFromPredecessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M prev prevTerms prevArgs next nextTerms nextArgs q tail : OTerm α),
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph prevTerms q)) →
    Nonempty (Derivation body Γ (memberGraph prevArgs tail)) →
    Nonempty (Derivation body Γ (memberGraph nextArgs (rawCons q tail)))

/-- Local head IH at a genuine typed window and actual head grammar,
and genuine well-scoped tail occurrence at its own actual grammar.
Both are moved to the same predecessor, in their respective axes. -/
def ExactOpenSelectedNonemptyArgsAtBounds : Prop :=
  ∀ (W : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M dq Mq da Ma qState qTerms qArgs aState aTerms aArgs
      prev prevTerms prevArgs next nextTerms nextArgs ctx ty q tail : OTerm α),
    Nonempty (Derivation body Γ (windowAt W ctx ty q)) →
    Nonempty (Derivation body Γ ((windowAt W ctx ty q).imp (memberGraph qTerms q))) →
    Nonempty (Derivation body Γ (observed dq H K Mq qState qTerms qArgs)) →
    Nonempty (Derivation body Γ (observed da H K Ma aState aTerms aArgs)) →
    Nonempty (Derivation body Γ (memberGraph aArgs tail)) →
    Nonempty (Derivation body Γ (ltF dq (suc d))) →
    Nonempty (Derivation body Γ (ltF Mq (suc M))) →
    Nonempty (Derivation body Γ (ltF da (suc d))) →
    Nonempty (Derivation body Γ (ltF Ma (suc M))) →
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph nextArgs (rawCons q tail)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
