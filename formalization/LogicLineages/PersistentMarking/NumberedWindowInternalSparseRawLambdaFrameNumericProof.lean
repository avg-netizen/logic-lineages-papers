module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run cursor field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (nodePacked codeOfNode)
open NumberedWindowRawContextAlgorithm (next context tick Frame)
open NumberedWindowInternalSparseRawFunctionFrame (encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape)
open NumberedWindowInternalSparseRawLambdaFrameNumericASTProof (guardOne guardBit value)
open NumberedWindowInternalSparseRawLambdaFrame

private theorem witnessOne (w : Nat) :
    run witnessShape w = 1 ↔ ∃ child, unpackNode w = some (1,[child]) := by
  change run (nodeGood (literal 1 1) 1) w = 1 ↔ _
  rw [nodeArity (literal 1 1) 1 w 1 (literalEvaluation 1 1 (w ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨child,_ | ⟨later,rest⟩⟩ <;> simp at arity
    exact ⟨child,h⟩
  · rintro ⟨child,h⟩
    exact ⟨[child],h,rfl⟩

private theorem termOne (q : Nat) :
    run termShape q = 1 ↔ ∃ d b, unpackNode q = some (2,[d,b]) := by
  change run (nodeGood (literal 1 2) 2) q = 1 ↔ _
  rw [nodeArity (literal 1 2) 2 q 2 (literalEvaluation 1 2 (q ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,arity⟩
    rcases xs with _ | ⟨d,_ | ⟨b,_ | ⟨last,rest⟩⟩⟩ <;> simp at arity
    exact ⟨d,b,h⟩
  · rintro ⟨d,b,h⟩
    exact ⟨[d,b],h,rfl⟩

private theorem witnessField {w child : Nat} (h : unpackNode w = some (1,[child])) :
    run (field 0) w = child := by
  rw [codeOfNode h]
  have t := (headTailOfCell (cellAt 1 (pack [child]))).2
  have c : run cellHead (pack [child]) = child := (headTailOfCell (cellAt child (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 1 (pack [child]) + 1) = child
  simp only [field,cursor,applyValue,t,c]

private theorem termFields {q d b : Nat} (h : unpackNode q = some (2,[d,b])) :
    run (field 0) q = d ∧ run (field 1) q = b := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 2 (pack [d,b]))).2
  have first : run cellHead (pack [d,b]) = d ∧ run cellTail (pack [d,b]) = pack [b] :=
    headTailOfCell (cellAt d (pack [b]))
  have last : run cellHead (pack [b]) = b := (headTailOfCell (cellAt b (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 2 (pack [d,b]) + 1) = d ∧ _
  simp only [field,cursor,applyValue,outer,first.1,first.2,last,packNode] <;> simp

private def Parsed (q w r b child e : Nat) : Prop :=
  ∃ d, unpackNode w = some (1,[child]) ∧ unpackNode q = some (2,[d,b]) ∧
    unpackNode r = some (2,[d,e])

private theorem guardReports (q w r : Nat) :
    evaluate frameGood (tape q w r) = 1 ↔ ∃ b child e, Parsed q w r b child e := by
  rw [guardOne,witnessOne,termOne,termOne]
  constructor
  · rintro ⟨⟨child,hw⟩,⟨d,b,hq⟩,⟨d',e,hr⟩,same⟩
    have dEq : d = d' := (termFields hq).1.symm.trans (same.trans (termFields hr).1)
    exact ⟨b,child,e,d,hw,hq,by simpa only [← dEq] using hr⟩
  · rintro ⟨b,child,e,d,hw,hq,hr⟩
    exact ⟨⟨child,hw⟩,⟨d,b,hq⟩,⟨d,e,hr⟩,(termFields hq).1.trans (termFields hr).1.symm⟩

private theorem actualNext (q r w b child e : Nat)
    (h : next 1 [w] q r = some (b,child,e)) :
    child = w ∧ ∃ d, unpackNode q = some (2,[d,b]) ∧ unpackNode r = some (2,[d,e]) := by
  cases hq : unpackNode q with
  | none => simp [next,hq] at h
  | some lhs =>
    cases hr : unpackNode r with
    | none => simp [next,hq,hr] at h
    | some rhs =>
      simp only [next,hq,hr,Option.bind_some] at h
      rcases lhs with ⟨ltag,ls⟩
      rcases rhs with ⟨rtag,rs⟩
      rcases ltag with _ | _ | _ | ltag <;>
        rcases ls with _ | ⟨d,_ | ⟨x,_ | ⟨later,rest⟩⟩⟩ <;> simp [context] at h
      rcases rtag with _ | _ | _ | rtag <;>
        rcases rs with _ | ⟨d',_ | ⟨y,_ | ⟨later,rest⟩⟩⟩ <;> simp [context] at h
      have seen : d = d' ∧ (x,w,y) = (b,child,e) := by
        simpa [beq_iff_eq,Prod.mk.injEq,and_assoc] using h
      obtain ⟨sameD,tuple⟩ := seen
      have fields : x = b ∧ w = child ∧ y = e := by
        simpa only [Prod.mk.injEq] using tuple
      obtain ⟨rfl,rfl,rfl⟩ := fields
      cases sameD
      exact ⟨rfl,d,by first | exact hq | rfl,by first | exact hr | rfl⟩

private theorem nextReports (q w r b child e : Nat) :
    tagOneNext q w r = some (b,child,e) ↔ Parsed q w r b child e := by
  constructor
  · intro h
    cases hw : unpackNode w with
    | none => simp [tagOneNext,hw] at h
    | some node =>
      rcases node with ⟨tag,fields⟩
      rcases tag with _ | _ | tag <;>
        rcases fields with _ | ⟨w',_ | ⟨later,rest⟩⟩ <;> simp [tagOneNext,hw] at h
      obtain ⟨same,d,hq,hr⟩ := actualNext q r w' b child e h
      rw [same]
      exact ⟨d,by first | exact hw | rfl,hq,hr⟩
  · rintro ⟨d,hw,hq,hr⟩
    simp [tagOneNext,hw,next,hq,hr,context]

theorem exact_AllRawLambdaFrame : ExactAllRawLambdaFrame := by
  intro q w r
  rw [value]
  cases h : tagOneNext q w r with
  | none =>
    rcases guardBit (tape q w r) with no | yes
    · simp only [no,if_pos,encodeFrame]
    · obtain ⟨b,child,e,fields⟩ := (guardReports q w r).mp yes
      have impossible := (nextReports q w r b child e).mpr fields
      rw [h] at impossible
      cases impossible
  | some out =>
    rcases out with ⟨b,child,e⟩
    have fields := (nextReports q w r b child e).mp h
    have yes := (guardReports q w r).mpr ⟨b,child,e,fields⟩
    obtain ⟨d,hw,hq,hr⟩ := fields
    have w0 := witnessField hw
    have q1 := (termFields hq).2
    have r1 := (termFields hr).2
    simp [yes,w0,q1,r1]

theorem exact_LiteralLambdaTick : ExactLiteralLambdaTick := by
  intro root status dom src child dst
  simp [tick,next,context,nodePacked]

#print axioms exact_AllRawLambdaFrame
#print axioms exact_LiteralLambdaTick
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameNumericProof
