module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder equalityOfAcceptance)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalAdditionLawsProof (leftZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (nodeGood exactBody field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail cellGood)
open NumberedWindowInternalFreshProbeDispatchProgram (literal zeroAt)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalSparseRawRunRootTapeProof (rejectLeft rejectRight)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralAtomicRawGuardProof
  (guardedRaw freeTest bottomTest atRawSource emitRawBottom exactRawBottom)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof
  (D atSourceGraph exact_OpenLiteralAtomicRawFreeGuard exact_OpenLiteralAtomicRawBottomGuard)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def freeTerm (t n : OTerm α) : OTerm α := rawCons z (packedBody [t,n])
def bottomTerm (t : OTerm α) : OTerm α := rawCons (numeral 3) (packedBody [t])

theorem freeReports (t n : OTerm α) :
    D B Γ (unary freeTest (suc z) (freeTerm t n)) ∧
      D B Γ (unary (field 0) t (freeTerm t n)) := by
  have tag : D B Γ (unary (literal 1 0) z (rawCons z (packedBody [t,n]))) := by
    unfold unary
    exact literalGraph 0 _
  have p := packedNode (body := B) (Γ := Γ) (literal 1 0) z [t,n] tag
  exact ⟨p.1,p.2.1⟩

private theorem missingFree (t : OTerm α) : D B Γ (unary freeTest z (bottomTerm t)) := by
  let code := bottomTerm t
  let tag := literal 1 0
  let tested : Program 1 := .composition equalityTest ![cellHead,tag]
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 3) (packedBody [t])
  have hg : D B Γ (unary cellGood (suc z) code) := ⟨Derivation.conjunctionLeft cell⟩
  have hh : D B Γ (unary cellHead (numeral 3) code) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have below : D B Γ (ltF z (numeral 3)) := by
    apply actualOriginalOrderIntroduction B α Γ z (numeral 3) (numeral 2)
    rw [onEquality]
    exact ⟨leftZero (suc (numeral 2))⟩
  have reject : D B Γ (unary tested z code) := by
    apply compositionValue equalityTest ![cellHead,tag] z ![code] ![numeral 3,z]
      (rejectBackwardOrder (numeral 3) z below)
    intro i
    exact Fin.cases hh (Fin.cases (literalGraph 0 ![code]) (fun j => Fin.elim0 j)) i
  have second := rejectLeft tested (applyUnary (exactBody 2) cellTail) ![code] reject
  exact rejectRight cellGood (conjunction tested (applyUnary (exactBody 2) cellTail)) ![code] hg second

private theorem emitFromFree (t n : OTerm α) :
    D B Γ (unary emitRawBottom (bottomTerm t) (freeTerm t n)) := by
  let code := freeTerm t n
  let tape : Fin 1 → OTerm α := ![code]
  have h₀ : D B Γ (unary (zeroAt 1) z code) := literalGraph 0 tape
  have ht := (freeReports (B := B) (Γ := Γ) t n).2
  have payload := consOfGraph (field 0) (zeroAt 1) t z tape ht h₀
  exact consOfGraph (literal 1 3) (consOf (field 0) (zeroAt 1)) (numeral 3) (rawCons t z)
    tape (literalGraph 3 tape) payload

/-- A successful atom-guarded raw call starting at an actual free
constructor ends at the literal bottom of the same stored type.
The result is in the original calculus, not inferred by calibration. -/
theorem exact_OpenLiteralGuardedFreeRawTarget (raw : Program 5) (ctx ty t n w r : OTerm α)
    (held : D B Γ (programGraph (guardedRaw raw) (suc z) ![ctx,ty,freeTerm t n,w,r])) :
    D B Γ (eqn r (bottomTerm t)) := by
  let tape : Fin 5 → OTerm α := ![ctx,ty,freeTerm t n,w,r]
  obtain ⟨guarded⟩ := exact_OpenLiteralAtomicRawFreeGuard raw tape (freeReports t n).1 held
  have accept : D B Γ (programGraph exactRawBottom (suc z) tape) := ⟨Derivation.conjunctionRight guarded⟩
  have emitted : D B Γ (programGraph (atRawSource emitRawBottom) (bottomTerm t) tape) :=
    atSourceGraph emitRawBottom (bottomTerm t) tape (emitFromFree t n)
  unfold exactRawBottom at accept
  rw [exact_DispatchControlAST.2.2.2.1] at accept
  have report := compositionRecover equalityTest
    (Fin.cons (.projection (4 : Fin 5)) (Fin.cons (atRawSource emitRawBottom) Fin.elim0))
    (suc z) tape ![r,bottomTerm t] accept (fun j =>
      Fin.cases (projectionValue 4 tape) (Fin.cases emitted (fun e => Fin.elim0 e)) j)
  exact equalityOfAcceptance r (bottomTerm t) report

/-- The actual literal bottom constructor cannot start any accepted
atom-guarded raw call at any open context/type/witness/destination. -/
theorem exact_OpenLiteralGuardedBottomRawReject (raw : Program 5) (ctx ty t w r : OTerm α)
    (held : D B Γ (programGraph (guardedRaw raw) (suc z) ![ctx,ty,bottomTerm t,w,r])) :
    D B Γ ⊥ := by
  have tag : D B Γ (unary (literal 1 3) (numeral 3) (rawCons (numeral 3) (packedBody [t]))) := by
    unfold unary
    exact literalGraph 3 _
  have bot := packedNode (body := B) (Γ := Γ) (literal 1 3) (numeral 3) [t] tag
  exact exact_OpenLiteralAtomicRawBottomGuard raw ![ctx,ty,bottomTerm t,w,r] (missingFree t) bot.1 held

#print axioms exact_OpenLiteralGuardedFreeRawTarget
#print axioms exact_OpenLiteralGuardedBottomRawReject
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawShapeProof
