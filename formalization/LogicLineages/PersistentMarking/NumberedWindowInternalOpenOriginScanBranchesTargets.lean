module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep rowCell)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

def ExactOpenOriginScanBranches : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed decoded row target dom cert rawLeft rawRight scratchLeft scratchRight
      tailLeft tailRight outLeft outRight : OrdinaryArithmetic.Term α),
    Reports r B Γ removed row decoded target dom cert →
    D B Γ (unary parser (suc scratchLeft) rawLeft) →
    D B Γ (unary parser (suc scratchRight) rawRight) →
    D B Γ (loopAccept r tailLeft rawLeft) → D B Γ (loopAccept r tailRight rawRight) →
    D B Γ (programGraph (rowStep true) outLeft ![row,tailLeft,scratchLeft]) →
    D B Γ (programGraph (rowStep false) outRight ![row,tailRight,scratchLeft]) →
    let L := programGraph scratchMember oneTerm ![scratchLeft,dom]
    let R := programGraph scratchMember oneTerm ![scratchRight,dom]
    (D B Γ L →
      D B Γ (rowCell outLeft row tailLeft) ∧ D B Γ (eqn outRight tailRight) ∧
      D B Γ (loopAccept r outLeft rawLeft) ∧ D B Γ (loopAccept r outRight rawRight)) ∧
    (D B Γ L.not → D B Γ R →
      D B Γ (eqn outLeft tailLeft) ∧ D B Γ (rowCell outRight row tailRight) ∧
      D B Γ (loopAccept r outLeft rawLeft) ∧ D B Γ (loopAccept r outRight rawRight))

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesTargets
