module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoveredWindowTargets (ownSeed)

def syntaxFlag (V : Program 1) : Program 1 := branch V (constantZero 1) (constantOne 1)

def ExactSyntaxFlagCalibration : Prop := ∀ (V : Program 1),
  ActualRawSyntax V → ActualRawSyntax (syntaxFlag V)

def ExactOwnCoverReports : Prop := ∀ (baseV M : Program 1) (G : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α),
  let V := syntaxFlag baseV
  let C := factoredCover V M G
  Nonempty (Derivation body Γ ((occursInCover C s seed seed).imp
    (unary V (suc z) seed ⊓ windowAt (ownSeed C s) ctx ty seed)))

end LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsTargets
