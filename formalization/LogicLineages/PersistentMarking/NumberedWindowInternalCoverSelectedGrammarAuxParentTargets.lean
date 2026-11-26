module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport termsPart)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)

/-- Physical introduction into the actual term part of the unchanged
selected successor, on the actual predecessor term scratch. -/
def ExactOpenSelectedAuxInTermPart : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args dom cod fn arg : OTerm α),
  Nonempty (Derivation body Γ (stepReport termsPart out H K ids terms args)) →
  Nonempty (Derivation body Γ (memberGraph K dom)) →
  Nonempty (Derivation body Γ (memberGraph K cod)) →
  Nonempty (Derivation body Γ (memberGraph terms fn)) →
  Nonempty (Derivation body Γ (memberGraph terms arg)) →
  Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg)))

/-- Install the same actual sparse tag-six key at an observed later
stage once both actual child keys occur in its observed predecessor. -/
def ExactOpenSelectedGrammarAuxAtPredecessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg : OTerm α),
  Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
  Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (memberGraph K dom)) →
  Nonempty (Derivation body Γ (memberGraph K cod)) →
  Nonempty (Derivation body Γ (memberGraph prevTerms fn)) →
  Nonempty (Derivation body Γ (memberGraph prevTerms arg)) →
  Nonempty (Derivation body Γ (memberGraph nextTerms (auxiliaryTerm dom cod fn arg)))

/-- A local parent rule for two real own-stage child occurrences. The
four paid inequalities and both actual type memberships are premises.
It neither asserts child own-cover nor derives measurement provenance
from a bound or a selected grammar report. -/
def ExactOpenSelectedGrammarAuxParent : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M df mf da ma fState fTerms fArgs aState aTerms aArgs
      prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg : OTerm α),
  Nonempty (Derivation body Γ (observed df H K mf fState fTerms fArgs)) →
  Nonempty (Derivation body Γ (observed da H K ma aState aTerms aArgs)) →
  Nonempty (Derivation body Γ (memberGraph fTerms fn)) →
  Nonempty (Derivation body Γ (memberGraph aTerms arg)) →
  Nonempty (Derivation body Γ (ltF df (suc d))) →
  Nonempty (Derivation body Γ (ltF mf (suc M))) →
  Nonempty (Derivation body Γ (ltF da (suc d))) →
  Nonempty (Derivation body Γ (ltF ma (suc M))) →
  Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
  Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (memberGraph K dom)) →
  Nonempty (Derivation body Γ (memberGraph K cod)) →
  Nonempty (Derivation body Γ (memberGraph nextTerms (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
