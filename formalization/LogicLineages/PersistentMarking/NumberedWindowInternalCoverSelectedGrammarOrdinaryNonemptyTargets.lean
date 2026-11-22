module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)

/-- Compose the one actual cons construction at dA+1 with one original
ordinary outer parent. The cons itself and enclosing scratch are unchanged.
All scopes and comparisons are actual reports. No measurement
provenance for these reports is asserted. -/
def ExactOpenSelectedGrammarOrdinaryNonemptyScratch : Prop :=
  ∀ (V Measure : Program 1) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (m d M dA MA dq Mq dr Mr qState qTerms qArgs rState rTerms rArgs
      prev prevTerms prevArgs consState consTerms consArgs vertices ctx ty h q r : OTerm α),
    let H := headsTerm s α
    let K := typesTerm s α
    let a := rawCons q r
    let key := ordinaryKey h a
    Nonempty (Derivation body Γ (windowAt W ctx ty q)) →
    Nonempty (Derivation body Γ ((windowAt W ctx ty q).imp (memberGraph qTerms q))) →
    Nonempty (Derivation body Γ (observed dq H K Mq qState qTerms qArgs)) →
    Nonempty (Derivation body Γ (observed dr H K Mr rState rTerms rArgs)) →
    Nonempty (Derivation body Γ (memberGraph rArgs r)) →
    Nonempty (Derivation body Γ (ltF dq (suc dA))) →
    Nonempty (Derivation body Γ (ltF Mq (suc MA))) →
    Nonempty (Derivation body Γ (ltF dr (suc dA))) →
    Nonempty (Derivation body Γ (ltF Mr (suc MA))) →
    Nonempty (Derivation body Γ (observed dA H K MA prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc dA) H K MA consState consTerms consArgs)) →
    Nonempty (Derivation body Γ (ltF (suc dA) (suc d))) →
    Nonempty (Derivation body Γ (ltF MA (suc M))) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (unary V (suc z) key)) →
    Nonempty (Derivation body Γ (unary Measure m key)) →
    Nonempty (Derivation body Γ (measurePair m d M)) →
    Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s) vertices key)) →
    Nonempty (Derivation body Γ (memberGraph vertices key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyTargets
