module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxExchangeCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open GorbowVerifierNormalization (normalize)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalSparseScalarEdge (packedEdge)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne compositeTwo compareEvaluation)
open NumberedWindowInternalLiteralEdgeObserverFitProof (WholeEdgeFit)
open NumberedWindowInternalLiteralTypedAuxExchangeCasesProof (exact_LiteralTypedAuxExchangeCases)

def readSlot (p : Program 1) (i : Fin 4) : Program 4 :=
  .composition p (Fin.cons (.projection i) Fin.elim0)

abbrev fieldSlot (i : Fin 4) (j : Nat) : Program 4 := readSlot (field j) i

def sameField (j : Nat) : Program 4 :=
  .composition compareNumbers (Fin.cons (fieldSlot 2 j) (Fin.cons (fieldSlot 3 j) Fin.elim0))

def functionType : Program 4 := consOf (fieldSlot 2 0) (fieldSlot 2 1)

def functionChildEdge (E : Program 4) : Program 4 :=
  .composition E ![.projection 0,functionType,fieldSlot 2 2,fieldSlot 3 2]

def argumentChildEdge (E : Program 4) : Program 4 :=
  .composition E ![.projection 0,fieldSlot 2 0,fieldSlot 2 3,fieldSlot 3 3]

/-- The two open branches each retain a smaller typed edge and the
unchanged component. Keep them distinct from the reduction witness. -/
def functionCase (E : Program 4) : Program 4 := conjunction (functionChildEdge E) (sameField 3)
def argumentCase (E : Program 4) : Program 4 := conjunction (sameField 2) (argumentChildEdge E)
def chooseChild (E : Program 4) : Program 4 := branch (normalize (functionCase E)) (argumentCase E) (constantOne 4)
def validateAuxiliary (E : Program 4) : Program 4 :=
  conjunction (readSlot termShape 3) (conjunction (sameField 0) (conjunction (sameField 1) (chooseChild E)))

def auxChildGuard (E : Program 4) : Program 4 := branch (readSlot termShape 2) (constantOne 4) (validateAuxiliary E)

/-- B is the actual original edge; E is the separately selected
smaller typed edge callback. The second conjunct is a genuine
proof-relevant accepted call, not an assumed property of B. -/
def typedAuxEdgeGuard (B E : Program 4) : Program 4 := conjunction B (auxChildGuard E)

private abbrev tape (ctx ty a b : Nat) : List.Vector Nat 4 := ctx ::ᵥ ty ::ᵥ a ::ᵥ b ::ᵥ nil

private theorem selectedValue (p : Program 1) (i : Fin 4) (xs : List.Vector Nat 4) :
    evaluate (readSlot p i) xs = run p (xs.get i) := by
  rw [readSlot,compositeOne]
  rfl

private theorem relatedBit (s : Settings) (E : Program 4) (h : WholeEdgeFit s E)
    (ctx ty a b : Nat) (g : List Nat) (opened : unpack ctx = some g) :
    evaluate E (tape ctx ty a b) = 1 ↔ edge s g ty a b = true := by
  have e : exactEdgeBit E ctx ty a b = packedEdge s ctx ty a b := congrFun (congrFun (congrFun (congrFun h ctx) ty) a) b
  rw [exactEdgeBit,packedEdge,opened,vectorFour] at e
  simpa [tape,edgeTape] using (Iff.of_eq (congrArg (· = true) e))

private theorem fieldOn {ctx ty a b d c f r d' c' f' r' : Nat}
    (ha : unpackNode a = some (6,[d,c,f,r])) (hb : unpackNode b = some (6,[d',c',f',r'])) :
    let xs := tape ctx ty a b
    (evaluate (fieldSlot 2 0) xs = d ∧ evaluate (fieldSlot 2 1) xs = c ∧
      evaluate (fieldSlot 2 2) xs = f ∧ evaluate (fieldSlot 2 3) xs = r) ∧
    (evaluate (fieldSlot 3 0) xs = d' ∧ evaluate (fieldSlot 3 1) xs = c' ∧
      evaluate (fieldSlot 3 2) xs = f' ∧ evaluate (fieldSlot 3 3) xs = r') := by
  dsimp only
  simp only [selectedValue]
  change (run (field 0) a = d ∧ run (field 1) a = c ∧ run (field 2) a = f ∧ run (field 3) a = r) ∧
    (run (field 0) b = d' ∧ run (field 1) b = c' ∧ run (field 2) b = f' ∧ run (field 3) b = r')
  exact ⟨termFields ha,termFields hb⟩

private theorem fourValue (p : Program 4) (inputs : Fin 4 → Program 4) (xs : List.Vector Nat 4) :
    evaluate (.composition p inputs) xs = evaluate p
      (evaluate (inputs 0) xs ::ᵥ evaluate (inputs 1) xs ::ᵥ evaluate (inputs 2) xs ::ᵥ evaluate (inputs 3) xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn _) = _
  rw [vectorFour]

private theorem calculate (E : Program 4) (ctx ty a b d c f u f' u' : Nat)
    (ha : unpackNode a = some (6,[d,c,f,u])) (hb : unpackNode b = some (6,[d,c,f',u']))
    (fit : (evaluate E (tape ctx (arrow d c) f f') = 1 ∧ u = u') ∨
      (f = f' ∧ evaluate E (tape ctx d u u') = 1)) :
    evaluate (validateAuxiliary E) (tape ctx ty a b) = 1 := by
  let xs := tape ctx ty a b
  obtain ⟨l,r⟩ := fieldOn (ctx := ctx) (ty := ty) ha hb
  have equals (j x y : Nat) (aRep : evaluate (fieldSlot 2 j) xs = x) (bRep : evaluate (fieldSlot 3 j) xs = y) :
      evaluate (sameField j) xs = if x = y then 1 else 0 := by
    rw [sameField,compositeTwo,aRep,bRep]
    exact compareEvaluation x y
  have type : evaluate functionType xs = arrow d c := by
    rw [functionType,consOf,compositeTwo,l.1,l.2.1,consValue]
    rfl
  have fn : evaluate (functionChildEdge E) xs = evaluate E (tape ctx (arrow d c) f f') := by
    rw [functionChildEdge,fourValue]
    change evaluate E (ctx ::ᵥ evaluate functionType xs ::ᵥ evaluate (fieldSlot 2 2) xs ::ᵥ
      evaluate (fieldSlot 3 2) xs ::ᵥ nil) = _
    rw [type,l.2.2.1,r.2.2.1]
  have arg : evaluate (argumentChildEdge E) xs = evaluate E (tape ctx d u u') := by
    rw [argumentChildEdge,fourValue]
    change evaluate E (ctx ::ᵥ evaluate (fieldSlot 2 0) xs ::ᵥ evaluate (fieldSlot 2 3) xs ::ᵥ
      evaluate (fieldSlot 3 3) xs ::ᵥ nil) = _
    rw [l.1,l.2.2.2,r.2.2.2]
  have active : evaluate (readSlot termShape 3) xs = 1 := by
    rw [selectedValue]
    exact (termOne b).mpr ⟨d,c,f',u',hb⟩
  have ch : evaluate (chooseChild E) xs = 1 := by
    rw [chooseChild,evalBranch,GorbowVerifierNormalization.Proof.actualEvaluation.2]
    rcases fit with left | right
    · have this : evaluate (functionCase E) xs = 1 := by
        rw [functionCase,actualConjunctionEvaluation,fn,equals 3 u u' l.2.2.2 r.2.2.2,left.1,if_pos left.2]
        rfl
      rw [this]
      rfl
    · have this : evaluate (argumentCase E) xs = 1 := by
        rw [argumentCase,actualConjunctionEvaluation,arg,equals 2 f f' l.2.2.1 r.2.2.1,right.2,if_pos right.1]
        rfl
      split
      · rfl
      · exact this
  change evaluate (validateAuxiliary E) xs = _
  rw [validateAuxiliary,actualConjunctionEvaluation,actualConjunctionEvaluation,actualConjunctionEvaluation,
    active,equals 0 d d l.1 r.1,equals 1 c c l.2.1 r.2.1,ch]
  simp

theorem exact_WholeTypedAuxEdgeGuard (s : Settings) (B E : Program 4)
    (base : WholeEdgeFit s B) (child : WholeEdgeFit s E) :
    WholeEdgeFit s (typedAuxEdgeGuard B E) := by
  funext ctx ty a b
  unfold exactEdgeBit
  rw [vectorFour]
  change decide (evaluate (typedAuxEdgeGuard B E) (tape ctx ty a b) = 1) = packedEdge s ctx ty a b
  rw [typedAuxEdgeGuard,actualConjunctionEvaluation]
  cases dec : unpack ctx with
  | none =>
    have missing : evaluate B (tape ctx ty a b) ≠ 1 := by
      intro on
      have h := congrFun (congrFun (congrFun (congrFun base ctx) ty) a) b
      rw [exactEdgeBit,vectorFour] at h
      change decide (evaluate B (tape ctx ty a b) = 1) = packedEdge s ctx ty a b at h
      simp [on,packedEdge,dec] at h
    simp [missing,packedEdge,dec]
  | some g =>
    rw [packedEdge,dec,Option.any_some]
    cases trueEdge : edge s g ty a b with
    | false =>
      have no : evaluate B (tape ctx ty a b) ≠ 1 := by
        intro actual
        have impossible := (relatedBit s B base ctx ty a b g dec).mp actual
        rw [trueEdge] at impossible
        contradiction
      simp [no]
    | true =>
      have yes := (relatedBit s B base ctx ty a b g dec).mpr trueEdge
      have checked : evaluate (auxChildGuard E) (tape ctx ty a b) = 1 := by
        rw [auxChildGuard,evalBranch,selectedValue]
        change (if run termShape a = 0 then 1 else evaluate (validateAuxiliary E) (tape ctx ty a b)) = 1
        by_cases isAux : run termShape a = 1
        · obtain ⟨d,c,f,u,ha⟩ := (termOne a).mp isAux
          obtain ⟨_,f',u',hb,split⟩ := exact_LiteralTypedAuxExchangeCases s g ty a b d c f u trueEdge ha
          rw [isAux,if_neg (by decide)]
          apply calculate E ctx ty a b d c f u f' u' ha hb
          rcases split with l | r
          · exact Or.inl ⟨(relatedBit s E child ctx (arrow d c) f f' g dec).mpr l.1,l.2⟩
          · exact Or.inr ⟨r.1,(relatedBit s E child ctx d u u' g dec).mpr r.2⟩
        · have zero : run termShape a = 0 := by
            unfold run termShape NumberedWindowInternalSparsePathEnvelope.nodeGood at *
            rw [actualConjunctionEvaluation] at isAux ⊢
            split
            · rename_i yes
              rw [if_pos yes] at isAux
              exact False.elim (isAux rfl)
            · rfl
          rw [zero,if_pos rfl]
      simp [yes,checked]

#print axioms exact_WholeTypedAuxEdgeGuard
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
