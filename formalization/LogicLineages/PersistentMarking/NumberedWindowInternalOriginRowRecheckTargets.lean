module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow oneTerm)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

def ExactOpenRecheckOriginRow : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removedOld removedSide row decodedOld decodedSide target dom cert : OrdinaryArithmetic.Term α),
    Reports r B Γ removedOld row decodedOld target dom cert →
    Nonempty (Derivation B Γ (unary parser (suc decodedSide) removedSide)) →
    Nonempty (Derivation B Γ (programGraph scratchMember oneTerm ![decodedSide,dom])) →
    Nonempty (Derivation B Γ (programGraph (insertedRow r) oneTerm ![removedSide,row]))

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckTargets
