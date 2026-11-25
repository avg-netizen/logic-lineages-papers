module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalFreshProbeDispatchProgram (literal zeroAt)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralAtomicRawGuardProof
  (guardedRaw atRawSource freeTest bottomTest emitRawBottom exactRawBottom)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D atSourceGraph)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm freeReports)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Rebuild the exact physically selected ordinary raw branch from
the original accepted child and the original tests' actual zero
outputs. This is not inferred from extensional program calibration. -/
theorem exact_OpenLiteralGuardedRawNonAtom (raw : Program 5) (xs : Fin 5 → OTerm α)
    (step : D B Γ (programGraph raw (suc z) xs))
    (free : D B Γ (unary freeTest z (xs 2))) (bottom : D B Γ (unary bottomTest z (xs 2))) :
    D B Γ (programGraph (guardedRaw raw) (suc z) xs) := by
  have normal := zeroBranchIntro (atRawSource bottomTest) raw (constantZero 5)
    (suc z) xs (atSourceGraph bottomTest z xs bottom) step
  exact zeroBranchIntro (atRawSource freeTest) (branch (atRawSource bottomTest) raw (constantZero 5))
    (conjunction raw exactRawBottom) (suc z) xs (atSourceGraph freeTest z xs free) normal

private theorem bottomEmitterAtFree (t n : OTerm α) :
    D B Γ (unary emitRawBottom (bottomTerm t) (freeTerm t n)) := by
  let code := freeTerm t n
  let tape : Fin 1 → OTerm α := ![code]
  have h₀ : D B Γ (unary (zeroAt 1) z code) := literalGraph 0 tape
  have ht := (freeReports (B := B) (Γ := Γ) t n).2
  have payload := consOfGraph (field 0) (zeroAt 1) t z tape ht h₀
  exact consOfGraph (literal 1 3) (consOf (field 0) (zeroAt 1)) (numeral 3) (rawCons t z)
    tape (literalGraph 3 tape) payload

/-- Rebuild the exact free arm when its reported raw destination really
is the literal typed bottom. The original raw derivation and the
bottom equality remain independent premises. -/
theorem exact_OpenLiteralGuardedFreeRawIntro (raw : Program 5) (ctx ty t n w r : OTerm α)
    (step : D B Γ (programGraph raw (suc z) ![ctx,ty,freeTerm t n,w,r]))
    (bottom : D B Γ (eqn r (bottomTerm t))) :
    D B Γ (programGraph (guardedRaw raw) (suc z) ![ctx,ty,freeTerm t n,w,r]) := by
  let xs : Fin 5 → OTerm α := ![ctx,ty,freeTerm t n,w,r]
  have emitted := atSourceGraph emitRawBottom (bottomTerm t) xs (bottomEmitterAtFree (B := B) (Γ := Γ) t n)
  have compare : D B Γ (programGraph exactRawBottom (suc z) xs) := by
    unfold exactRawBottom
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest
      (Fin.cons (.projection (4 : Fin 5)) (Fin.cons (atRawSource emitRawBottom) Fin.elim0))
      (suc z) xs ![r,bottomTerm t] (equalityOfEqual r (bottomTerm t) bottom)
    exact fun i => Fin.cases (projectionValue 4 xs) (Fin.cases emitted (fun e => Fin.elim0 e)) i
  have accepted := conjunctionAccept raw exactRawBottom xs step compare
  exact successorBranchIntro (atRawSource freeTest) (branch (atRawSource bottomTest) raw (constantZero 5))
    (conjunction raw exactRawBottom) (suc z) z xs (atSourceGraph freeTest (suc z) xs (freeReports t n).1) accepted

#print axioms exact_OpenLiteralGuardedRawNonAtom
#print axioms exact_OpenLiteralGuardedFreeRawIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawIntroProof
