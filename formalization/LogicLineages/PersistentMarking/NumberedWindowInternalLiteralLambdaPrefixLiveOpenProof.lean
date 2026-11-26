module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackForceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue headTransport)
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparseRawTick (emitState)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph emitGraph)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralLambdaFrameProof
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaFallbackForceProof (exact_OpenLambdaHeaderTest)
open NumberedWindowInternalLiteralLambdaLexicalGateProof
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof

attribute [local irreducible] programGraph
abbrev bit5 {α : Type} (p : Program 5) (xs : Fin 5 → OTerm α) : Formula α := programGraph p (suc z) xs
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixTest (c t q w r d a inner e b : OTerm α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (row : LambdaParts B Γ q w r d a inner e b) :
    D B Γ (bit5 isLambdaPrefix ![c,t,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  let n := lambdaWitnessTerm inner
  have lits : D B Γ (unary (literal 1 1) (numeral 1) n) := literalGraph 1 ![n]
  have shape : D B Γ (unary lambdaWitnessShape (suc z) n) :=
    (packedNode (literal 1 1) (numeral 1) [inner] lits).1
  have wit := headTransport lambdaWitnessShape (suc z) n w Fin.elim0
    (row.witness.map symm) shape
  have test : D B Γ (bit lambdaWitnessTest ![q,w,r]) := onTape lambdaWitnessShape 1 (suc z) ![q,w,r] wit
  have liftTest (p : Program 3) (h : D B Γ (bit p ![q,w,r])) :
      D B Γ (bit5 (rawTripleCall p) xs) := by
    apply compositionValue p ![.projection 2,.projection 3,.projection 4] (suc z) xs ![q,w,r] h
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (fun e => Fin.elim0 e))) i
  exact conjunctionAccept _ _ xs (liftTest _ (exact_OpenLambdaHeaderTest q w r head)) (liftTest _ test)

theorem exact_OpenPrefixValidationRows (W : Program 3) (c t q w r : OTerm α)
    (accepted : D B Γ (bit5 (prefixValidation W) ![c,t,q,w,r])) :
    D B Γ (bit5 (lambdaLexicalGate W) ![c,t,q,w,r]) := by
  obtain ⟨row⟩ := conjunctionRecover (rawTripleCall lambdaFrameGuard) (lambdaLexicalGate W) _ accepted
  exact ⟨Derivation.conjunctionRight row⟩

theorem exact_OpenPrefixLifts (W : Program 3) (c t q w r d k a inner b : OTerm α)
    (frameTest : D B Γ (bit5 isLambdaPrefix ![c,t,q,w,r]))
    (validated : D B Γ (bit5 (prefixValidation W) ![c,t,q,w,r]))
    (binder : D B Γ (unary (field 0) d q))
    (coding : D B Γ (unary cellTail k t))
    (src : D B Γ (unary (field 1) a q))
    (cert : D B Γ (unary (field 0) inner w))
    (dst : D B Γ (unary (field 1) b r)) :
    D B Γ (programGraph (prefixTick W)
      (prefixStartTerm (rawCons d c) k a inner b) ![prefixStartTerm c t q w r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  let after := prefixStartTerm (rawCons d c) k a inner b
  let frame := prefixFrameTerm (rawCons d c) k a inner b
  have ctx : D B Γ (programGraph lexicalContext (rawCons d c) xs) :=
    consOfGraph lexicalBinder (.projection 0) d c xs (lexicalSlotAt (field 0) 2 d xs binder) (projectionValue 0 xs)
  have out : D B Γ (programGraph prefixNext frame xs) :=
    exact_OpenPrefixFrameEmit lexicalContext lexicalCodomain lexicalSourceBody prefixInnerWitness lexicalTargetBody
      xs (rawCons d c) k a inner b ctx (lexicalSlotAt cellTail 1 k xs coding)
      (lexicalSlotAt (field 1) 2 a xs src) (lexicalSlotAt (field 0) 3 inner xs cert)
      (lexicalSlotAt (field 1) 4 b xs dst)
  have emit : D B Γ (programGraph (emitState (ID1Completion.InternalLessThan.constantOne 5) prefixNext) after xs) :=
    emitGraph _ _ (suc z) frame xs (oneConstantValue xs) out
  have live : D B Γ (programGraph (prefixLive W) after xs) :=
    successorBranchIntro isLambdaPrefix prefixAccept _ after z xs frameTest
      (successorBranchIntro (prefixValidation W) prefixReject _ after z xs validated emit)
  exact exact_OpenPrefixTickAtFrame W (suc z) c t q w r after live

theorem exact_OpenPrefixRejects (W : Program 3) (c t q w r : OTerm α)
    (frameTest : D B Γ (bit5 isLambdaPrefix ![c,t,q,w,r]))
    (invalid : D B Γ (programGraph (prefixValidation W) z ![c,t,q,w,r])) :
    D B Γ (programGraph (prefixTick W) (stateTerm z z) ![prefixStartTerm c t q w r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  have reject : D B Γ (programGraph prefixReject (stateTerm z z) xs) :=
    emitGraph _ _ z z xs (constantZeroValue xs) (constantZeroValue xs)
  have live : D B Γ (programGraph (prefixLive W) (stateTerm z z) xs) :=
    successorBranchIntro isLambdaPrefix prefixAccept _ _ z xs frameTest
      (zeroBranchIntro (prefixValidation W) prefixReject _ _ xs invalid reject)
  exact exact_OpenPrefixTickAtFrame W (suc z) c t q w r (stateTerm z z) live

#print axioms exact_OpenPrefixTest
#print axioms exact_OpenPrefixValidationRows
#print axioms exact_OpenPrefixLifts
#print axioms exact_OpenPrefixRejects
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof
