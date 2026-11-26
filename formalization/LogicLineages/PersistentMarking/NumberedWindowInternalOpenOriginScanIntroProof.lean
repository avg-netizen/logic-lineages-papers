module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalRawListRecursionProof (consValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectInsertedRowTargets
  (insertedRow oneTerm parseRemoved poolReady poolCode)
open NumberedWindowInternalDirectInsertedScanTargets
  (scanBase scanStep rowAt scanLoop scanAt)
open NumberedWindowInternalOpenOriginScanIntroTargets

attribute [local irreducible] programGraph
local notation "T" => OrdinaryArithmetic.Term

theorem exact_OpenOriginScanConsIntro : ExactOpenOriginScanConsIntro := by
  intro r B α Γ code head tail removed cons checked tailOK
  let xs : Fin 3 → T α := Fin.cons head (Fin.cons oneTerm ![removed])
  have row : D B Γ (programGraph (rowAt r) oneTerm xs) := by
    apply compositionValue (insertedRow r) ![.projection 2,.projection 0]
      oneTerm xs ![removed,head] checked
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 0 xs)
      (fun j => Fin.elim0 j)) i
  have step : D B Γ (programGraph (scanStep r) oneTerm xs) :=
    conjunctionAccept (rowAt r) (.projection 1) xs row (projectionValue 1 xs)
  exact consValue scanBase (scanStep r) code head tail oneTerm oneTerm ![removed] cons tailOK step

theorem exact_OpenOriginRawScanIntro : ExactOpenOriginRawScanIntro := by
  intro r B α Γ raw rows removed parsed checked
  let xs : Fin 2 → T α := ![raw,removed]
  have parsedAt : D B Γ (programGraph parseRemoved (suc rows) xs) := by
    apply compositionValue parser ![.projection 0] (suc rows) xs ![raw] parsed
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have ready : D B Γ (programGraph poolReady oneTerm xs) :=
    successorBranchIntro parseRemoved (constantZero 2) (literal 2 1)
      oneTerm rows xs parsedAt (literalGraph 1 xs)
  have bodyCode : D B Γ (programGraph poolCode rows xs) := by
    apply compositionValue predecessor ![parseRemoved] rows xs ![suc rows]
      (predecessorSuccessor rows)
    intro i
    obtain rfl := Fin.eq_zero i
    exact parsedAt
  have loop : D B Γ (programGraph (scanAt r) oneTerm xs) := by
    apply compositionValue (scanLoop r) ![poolCode,.projection 1] oneTerm xs
      (Fin.cons rows ![removed]) checked
    intro i
    exact Fin.cases bodyCode (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i
  exact conjunctionAccept poolReady (scanAt r) xs ready loop

#print axioms exact_OpenOriginScanConsIntro
#print axioms exact_OpenOriginRawScanIntro

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroProof
