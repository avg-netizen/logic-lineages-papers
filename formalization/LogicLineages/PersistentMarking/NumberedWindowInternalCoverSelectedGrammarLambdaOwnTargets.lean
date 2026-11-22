module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

def OpenSelectedPartContainsLambda (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args ty q : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph terms q)) →
    Nonempty (Derivation body Γ (memberGraph out (lambdaTerm ty q)))

/-- The actual selected predecessor/successor pair uses one physical K
and the original tag-two layer; the child is already in the predecessor. -/
def ExactOpenSelectedGrammarLambdaFromPredecessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width prev prevTerms prevArgs next out args ty q : OTerm α),
    Nonempty (Derivation body Γ (observed d H K width prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K width next out args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph prevTerms q)) →
    Nonempty (Derivation body Γ (memberGraph out (lambdaTerm ty q)))

/-- Separate local induction: one genuine child observation and own key
at lower coordinates, one actual parent predecessor and successor. -/
def ExactOpenSelectedGrammarLambdaAtBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width childD childW childState childTerms childArgs
      prev prevTerms prevArgs next out args ty q : OTerm α),
    Nonempty (Derivation body Γ (observed childD H K childW childState childTerms childArgs)) →
    Nonempty (Derivation body Γ (memberGraph childTerms q)) →
    Nonempty (Derivation body Γ (ltF childD (suc d))) →
    Nonempty (Derivation body Γ (ltF childW (suc width))) →
    Nonempty (Derivation body Γ (observed d H K width prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K width next out args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph out (lambdaTerm ty q)))

/-- Conditional own-cover at the actual tag-two measured coordinate
equation: depth increases by one; numeral coordinate does not change.
The genuine typed body is in its supplied context/type and invokes only
the local own-key IH at that same body and its own observed grammar. -/
def ExactOpenSelectedGrammarLambdaMeasuredScratch : Prop :=
  ∀ (V Measure : Program 1) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (m mc d width childState childTerms childArgs vertices ctx bodyTy ty q : OTerm α),
    Nonempty (Derivation body Γ (windowAt W ctx bodyTy q)) →
    Nonempty (Derivation body Γ ((windowAt W ctx bodyTy q).imp
      ((unary (scratchVertices (selectedCover V Measure) s) childTerms q).imp
        (memberGraph childTerms q)))) →
    Nonempty (Derivation body Γ (observed d
      (headsTerm s α) (typesTerm s α)
      width childState childTerms childArgs)) →
    Nonempty (Derivation body Γ (unary V (suc z) q)) →
    Nonempty (Derivation body Γ (unary Measure mc q)) →
    Nonempty (Derivation body Γ (codePair mc d width)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (unary V (suc z) (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (unary Measure m (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (measurePair m d width)) →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V Measure) s) vertices (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
