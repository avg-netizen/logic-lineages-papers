module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageNumericCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoNumericStepProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalRawListRecursion (lookup)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorTwo)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowInternalAuxExchangeMemoStepTargets
  (TermSyntaxCalibrated unaryAfter binaryAfter rawSource rawTarget)
open NumberedWindowInternalAuxExchangeMemoStepDataProof
  (args foundKey unaryValue binaryValue conjunctionOne conjunctionBit)
open NumberedWindowRawExchangeVerticesCodecProof (getFieldLt)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAtomicApplicationTableProof (rowAuxPair)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowInternalLiteralBiAuxRawMemoStageProof
open NumberedWindowInternalLiteralTypedMemoStageProof (typedMemoStage stageGuard childOnCarrier)
open NumberedWindowInternalLiteralTypedMemoEvaluationProof
open NumberedWindowInternalLiteralTypedMemoStageNumericCasesProof

private theorem smallerPair (p q a b : Nat) (l : p < a) (r : q < b) : pair p q < pair a b := by
  let x := p+q
  let y := a+b
  have slope : x+1 ≤ y := by dsimp [x,y]; omega
  have between : (x+1)*(x+1) ≤ y*y := Nat.mul_le_mul slope slope
  have start : x*x + p < (x+1)*(x+1) := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    dsimp [x]
    omega
  exact Nat.lt_of_lt_of_le start (Nat.le_trans between (Nat.le_add_right _ a))

private theorem baseAt (s : Settings) (X : Program 2) (fit : ActualTermExchange s X) (a b : Nat) :
    evaluate X (a ::ᵥ b ::ᵥ nil) = ((bits s.equivalentHeads a b).1).toNat := by
  have left : exchangeTape a b 0 = a := rfl
  have right : exchangeTape a b 1 = b := rfl
  have h := fit a b
  rw [vectorTwo,left,right] at h
  exact h

/-- At every decoded literal pair key the new scratch branch does not
invent an edge. Its auxiliary branch is justified through strictly
earlier actual rows and the two original syntax checks. -/
theorem exact_LiteralBiAuxRawMemoStep (s : Settings) (X : Program 2) (V : Program 1)
    (fit : ActualTermExchange s X) (valid : TermSyntaxCalibrated V) (i old a b : Nat)
    (key : i+1 = pair a b)
    (earlier : ∀ p q, pair p q < i+1 →
      evaluate lookup ((i - pair p q) ::ᵥ old ::ᵥ nil) = ((bits s.equivalentHeads p q).1).toNat) :
    evaluate (rawAuxMemoStage X V) (tape i old 0 0) = ((bits s.equivalentHeads a b).1).toNat := by
  let xs := tape i old 0 0
  have decoded := foundKey i old a b (by rw [key,encodedPair])
  have fact := conjunctionBit (unaryAfter termShape rawSource)
    (conjunction (unaryAfter V rawSource) (conjunction (unaryAfter V rawTarget)
      (typedMemoStage (constantOne 4)))) xs
  change evaluate (rawAuxMemoGate V) xs = 0 ∨ evaluate (rawAuxMemoGate V) xs = 1 at fact
  rcases fact with plain | live
  · rw [rawAuxMemoStage,evalBranch,plain,if_pos rfl,binaryValue,decoded.2.1,decoded.2.2]
    exact baseAt s X fit a b
  · have selected := live
    rw [rawAuxMemoGate,conjunctionOne,conjunctionOne,conjunctionOne,
      unaryValue,unaryValue,unaryValue,decoded.2.1,decoded.2.2] at selected
    obtain ⟨shape,goodA,goodB,inner⟩ := selected
    rw [valid] at goodA goodB
    have syntaxA : (syntaxBits a).1 = true := by cases h : (syntaxBits a).1 <;> simp_all
    have syntaxB : (syntaxBits b).1 = true := by cases h : (syntaxBits b).1 <;> simp_all
    rw [exact_LiteralTypedMemoStageTape (constantOne 4) 0 old i a b key] at inner
    obtain ⟨d,c,f,u,ha⟩ := (termOne a).mp shape
    obtain ⟨f',u',hb,paths⟩ := exact_LiteralTypedMemoStageNumericCases (childOnCarrier (constantOne 4))
      (carrierCode 0 old i) 0 a b d c f u ha inner
    have recovered (t p q : Nat) (lp : p < a) (lq : q < b)
        (h : evaluate (childOnCarrier (constantOne 4)) (tape (carrierCode 0 old i) t p q) = 1) :
        (row s.equivalentHeads p q).1 = true := by
      have smaller := smallerPair p q a b lp lq
      rw [← key] at smaller
      have picked := ((exact_LiteralTypedMemoChildNumerals (constantOne 4) 0 old i t p q).mp h).2.1
      rw [earlier p q smaller] at picked
      have yes : (bits s.equivalentHeads p q).1 = true := by
        cases branch : (bits s.equivalentHeads p q).1 <;> simp [branch] at picked ⊢
      simp only [bits,Bool.and_eq_true] at yes
      exact yes.2
    have ea : a = auxRaw d c f u := codeOfNode ha
    have eb : b = auxRaw d c f' u' := codeOfNode hb
    have parent : (row s.equivalentHeads a b).1 = true := by
      rw [ea,eb,rowAuxPair]
      rcases paths with fn | arg
      · have small := recovered (arrow d c) f f' (getFieldLt ha 2) (getFieldLt hb 2) fn.1
        simp [small,fn.2]
      · have small := recovered d u u' (getFieldLt ha 3) (getFieldLt hb 3) arg.2
        simp [small,arg.1]
    have bit : (bits s.equivalentHeads a b).1 = true := by
      simp [bits,syntaxA,syntaxB,parent]
    rw [rawAuxMemoStage,evalBranch,live,if_neg (by decide),bit]
    rfl

#print axioms exact_LiteralBiAuxRawMemoStep
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoNumericStepProof
