module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal zeroAt)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest emitRawBottom)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm freeReports)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot atomicFallback rootBottomComparison)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem freeEmitter (t n : OTerm α) :
    D B Γ (unary emitRawBottom (bottomTerm t) (freeTerm t n)) := by
  let code := freeTerm t n
  let xs : Fin 1 → OTerm α := ![code]
  have typed := (freeReports (B := B) (Γ := Γ) t n).2
  have tail := consOfGraph (field 0) (zeroAt 1) t z xs typed (literalGraph 0 xs)
  exact consOfGraph (literal 1 3) (consOf (field 0) (zeroAt 1))
    (numeral 3) (rawCons t z) xs (literalGraph 3 xs) tail

/-- Free-variable checks at the actual root callback force its exact
typed bottom while keeping the original witness payload arbitrary. -/
theorem exact_OpenLiteralAtomicRootFreeTarget (p : Program 3) (t n w r : OTerm α)
    (held : D B Γ (programGraph (atomicRoot p) (suc z) ![freeTerm t n,w,r])) :
    D B Γ (eqn r (bottomTerm t)) := by
  let xs : Fin 3 → OTerm α := ![freeTerm t n,w,r]
  have free := onTape freeTest 0 (suc z) xs (freeReports (B := B) (Γ := Γ) t n).1
  have arm := successorBranchElim (onRaw freeTest 0) (branch (onRaw bottomTest 0) p (constantZero 3))
    (conjunction p rootBottomComparison) (suc z) z xs free held
  obtain ⟨out⟩ := conjunctionRecover p rootBottomComparison xs arm
  have compare : D B Γ (programGraph rootBottomComparison (suc z) xs) :=
    ⟨Derivation.conjunctionRight out⟩
  have value := onTape emitRawBottom 0 (bottomTerm t) xs (freeEmitter (B := B) (Γ := Γ) t n)
  unfold rootBottomComparison at compare
  rw [exact_DispatchControlAST.2.2.2.1] at compare
  have actual := compositionRecover equalityTest
    (Fin.cons (.projection (2 : Fin 3)) (Fin.cons (onRaw emitRawBottom 0) Fin.elim0))
    (suc z) xs ![r,bottomTerm t] compare
    (fun j => Fin.cases (projectionValue 2 xs) (Fin.cases value (fun k => Fin.elim0 k)) j)
  exact equalityOfAcceptance r (bottomTerm t) actual

/-- The ordinary fallback graph is physically zero at an actual
free test, for any original witness and destination. -/
theorem exact_OpenLiteralAtomicFallbackFree (p : Program 3) (q w r : OTerm α)
    (free : D B Γ (unary freeTest (suc z) q)) :
    D B Γ (programGraph (atomicFallback p) z ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  exact successorBranchIntro (onRaw freeTest 0) (branch (onRaw bottomTest 0) p (constantZero 3))
    (constantZero 3) z z xs (onTape freeTest 0 (suc z) xs free) (constantZeroValue xs)

/-- Both selected callbacks are physically zero on the actual bottom
branch. The reported zero free test prevents selecting a different
branch; no assertion about numeric rank is used. -/
theorem exact_OpenLiteralAtomicTickBottomCallbacks (p other : Program 3) (q w r : OTerm α)
    (notFree : D B Γ (unary freeTest z q)) (isBottom : D B Γ (unary bottomTest (suc z) q)) :
    D B Γ (programGraph (atomicRoot p) z ![q,w,r]) ∧
    D B Γ (programGraph (atomicFallback other) z ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  have no := onTape freeTest 0 z xs notFree
  have yes := onTape bottomTest 0 (suc z) xs isBottom
  have inner : ∀ f : Program 3, D B Γ (programGraph (branch (onRaw bottomTest 0) f (constantZero 3)) z xs) := by
    intro f
    exact successorBranchIntro (onRaw bottomTest 0) f (constantZero 3) z z xs yes (constantZeroValue xs)
  exact ⟨zeroBranchIntro (onRaw freeTest 0) (branch (onRaw bottomTest 0) p (constantZero 3))
      (conjunction p rootBottomComparison) z xs no (inner p),
    zeroBranchIntro (onRaw freeTest 0) (branch (onRaw bottomTest 0) other (constantZero 3))
      (constantZero 3) z xs no (inner other)⟩

#print axioms exact_OpenLiteralAtomicRootFreeTarget
#print axioms exact_OpenLiteralAtomicFallbackFree
#print axioms exact_OpenLiteralAtomicTickBottomCallbacks
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickOpenProof
