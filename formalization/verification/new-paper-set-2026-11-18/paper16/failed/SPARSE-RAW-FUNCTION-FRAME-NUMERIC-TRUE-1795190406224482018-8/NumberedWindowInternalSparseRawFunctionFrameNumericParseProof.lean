module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run cursor field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape guardOne)

theorem witnessOne (w : Nat) :
    run witnessShape w = 1 ↔ ∃ child, unpackNode w = some (5,[child]) := by
  change run (nodeGood (literal 1 5) 1) w = 1 ↔ _
  rw [nodeArity (literal 1 5) 1 w 5 (literalEvaluation 1 5 (w ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨child,_ | ⟨later,rest⟩⟩ <;> simp at arity
    exact ⟨child,h⟩
  · rintro ⟨child,h⟩
    exact ⟨[child],h,rfl⟩

theorem termOne (q : Nat) :
    run termShape q = 1 ↔ ∃ d t f a, unpackNode q = some (6,[d,t,f,a]) := by
  change run (nodeGood (literal 1 6) 4) q = 1 ↔ _
  rw [nodeArity (literal 1 6) 4 q 6 (literalEvaluation 1 6 (q ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨d,_ | ⟨t,_ | ⟨f,_ | ⟨a,_ | ⟨last,rest⟩⟩⟩⟩⟩ <;> simp at arity
    exact ⟨d,t,f,a,h⟩
  · rintro ⟨d,t,f,a,h⟩
    exact ⟨[d,t,f,a],h,rfl⟩

theorem witnessField {w child : Nat} (h : unpackNode w = some (5,[child])) :
    run (field 0) w = child := by
  rw [codeOfNode h]
  have t := (headTailOfCell (cellAt 5 (pack [child]))).2
  have c : run cellHead (pack [child]) = child := (headTailOfCell (cellAt child (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 5 (pack [child]) + 1) = child
  simp only [field,cursor,applyValue,t,c]

theorem termFields {q d t f a : Nat} (h : unpackNode q = some (6,[d,t,f,a])) :
    run (field 0) q = d ∧ run (field 1) q = t ∧ run (field 2) q = f ∧ run (field 3) q = a := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 6 (pack [d,t,f,a]))).2
  have first : run cellHead (pack [d,t,f,a]) = d ∧ run cellTail (pack [d,t,f,a]) = pack [t,f,a] :=
    headTailOfCell (cellAt d (pack [t,f,a]))
  have second : run cellHead (pack [t,f,a]) = t ∧ run cellTail (pack [t,f,a]) = pack [f,a] :=
    headTailOfCell (cellAt t (pack [f,a]))
  have third : run cellHead (pack [f,a]) = f ∧ run cellTail (pack [f,a]) = pack [a] :=
    headTailOfCell (cellAt f (pack [a]))
  have last : run cellHead (pack [a]) = a := (headTailOfCell (cellAt a (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 6 (pack [d,t,f,a]) + 1) = d ∧ _
  simp only [field,cursor,applyValue,outer,first.1,first.2,second.1,second.2,third.1,third.2,last,
    packNode] <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- Code-level description of the actual source case, before choosing
a scratch output representation. No constraints on the child payload. -/
def FrameReport (q w r f child g : Nat) : Prop :=
  ∃ dom cod arg,
    unpackNode w = some (5,[child]) ∧
    unpackNode q = some (6,[dom,cod,f,arg]) ∧
    unpackNode r = some (6,[dom,cod,g,arg])

theorem guardReports (q w r : Nat) :
    evaluate frameGood (tape q w r) = 1 ↔ ∃ f child g, FrameReport q w r f child g := by
  rw [guardOne,witnessOne,termOne,termOne]
  constructor
  · rintro ⟨⟨child,hw⟩,⟨d,t,f,a,hq⟩,⟨d',t',g,a',hr⟩,hd,ht,ha⟩
    obtain ⟨q0,q1,_,q3⟩ := termFields hq
    obtain ⟨r0,r1,_,r3⟩ := termFields hr
    have sameD : d = d' := q0.symm.trans (hd.trans r0)
    have sameT : t = t' := q1.symm.trans (ht.trans r1)
    have sameA : a = a' := q3.symm.trans (ha.trans r3)
    exact ⟨f,child,g,d,t,a,hw,hq,by simpa only [← sameD,← sameT,← sameA] using hr⟩
  · rintro ⟨f,child,g,d,t,a,hw,hq,hr⟩
    obtain ⟨q0,q1,_,q3⟩ := termFields hq
    obtain ⟨r0,r1,_,r3⟩ := termFields hr
    exact ⟨⟨child,hw⟩,⟨d,t,f,a,hq⟩,⟨d,t,g,a,hr⟩,
      q0.trans r0.symm,q1.trans r1.symm,q3.trans r3.symm⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
