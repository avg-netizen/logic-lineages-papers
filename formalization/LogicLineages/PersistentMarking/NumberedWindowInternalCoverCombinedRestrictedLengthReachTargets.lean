module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edgeGraph edge4)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets (CrossCoverReports)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

def ExactOpenCoverLengthReach : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty vertices a b fuel pool : OTerm α),
    Nonempty (Derivation body Γ (unary poolLength (suc fuel) vertices)) →
    Nonempty (Derivation body Γ (memberGraph vertices a)) →
    Nonempty (Derivation body Γ (memberGraph vertices b)) →
    Nonempty (Derivation body Γ (acceptEdge E ctx ty a b)) →
    Nonempty (Derivation body Γ (programGraph (members E) pool (membersTape vertices ctx ty a))) →
    Nonempty (Derivation body Γ (memberGraph pool b))

/-- One original edge from the actual seed into the same actual scratch.
The strict successor length remains a real explicit program report. -/
def ExactOpenCoverPackedLengthReach : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty vertices a b fuel pool : OTerm α),
    Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices a)) →
    Nonempty (Derivation body Γ (unary poolLength (suc fuel) vertices)) →
    Nonempty (Derivation body Γ (memberGraph vertices a)) →
    Nonempty (Derivation body Γ (memberGraph vertices b)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx ty a b)) →
    Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,a])) →
    Nonempty (Derivation body Γ (memberGraph pool b))

/-- Specialization to the exact chosen P/C/Wp and actual paired guarded X.
The continued cross-cover reports all refer to the very same raw list. -/
def ExactOpenCoverCombinedRestrictedPairedLengthReach : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg vertices fuel pool : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    CrossCoverReports P.cover s body Γ a b vertices →
    Nonempty (Derivation body Γ (unary poolLength (suc fuel) vertices)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod a b)) →
    Nonempty (Derivation body Γ (programGraph (membersAtSeed P.cover X W s) pool ![ctx,cod,a])) →
    Nonempty (Derivation body Γ (memberGraph pool b))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets
