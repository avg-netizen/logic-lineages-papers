module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (Address addressView contextView typeBit)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFieldAlgorithm (pack unpack packNode unpackNode)
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood field cursor)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (packOfUnpack cellAt codeOfCell flagOfCell headTailOfCell noFlagOfNone nodeOfCell noNode)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue nodeArity)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterNumericTargets

private theorem contextUnpack {raw : Nat} {ctx : List Nat}
    (h : contextView raw = some ctx) : unpack raw = some ctx := by
  unfold contextView at h
  cases hu : unpack raw with
  | none => simp [hu] at h
  | some xs =>
    have parsed : (∀ x ∈ xs, typeBit x = true) ∧ xs = ctx := by
      simpa [hu] using h
    exact congrArg some parsed.2

/-- Recover the literal tag and original packed context, without
replacing either context or result type validation by an arity test. -/
private theorem positiveView {q : Nat} {ctx : List Nat} {r k : Nat}
    (h : addressView q = some (ctx,r,k)) : unpackNode q = some (3,[pack ctx,r,k]) := by
  cases hu : unpackNode q with
  | none => simp [addressView,hu] at h
  | some node =>
    rcases node with ⟨tag,fields⟩
    rcases tag with _ | _ | _ | _ | tag <;>
      rcases fields with _ | ⟨m,_ | ⟨ty,_ | ⟨tm,_ | ⟨next,rest⟩⟩⟩⟩ <;>
      simp [addressView,hu] at h
    cases hc : contextView m with
    | none => simp [hc] at h
    | some stack =>
      cases ht : typeBit ty with
      | false => simp [hc,ht] at h
      | true =>
        have same : (stack,ty,tm) = (ctx,r,k) := by simpa [hc,ht] using h
        have h0 : stack = ctx := congrArg Prod.fst same
        have h1 : ty = r := congrArg (fun a : Address => a.2.1) same
        have h2 : tm = k := congrArg (fun a : Address => a.2.2) same
        have spine := packOfUnpack m (contextUnpack hc)
        rw [spine,h0,h1,h2]

private theorem codeOfPositiveNode {q tag : Nat} {xs : List Nat}
    (h : unpackNode q = some (tag,xs)) : q = packNode tag xs := by
  cases hc : chosenCell q with
  | none => rw [noNode hc] at h; cases h
  | some pair =>
    rcases pair with ⟨a,t⟩
    rw [nodeOfCell hc] at h
    cases ht : unpack t with
    | none => rw [ht] at h; cases h
    | some fs =>
      rw [ht] at h
      have same : (a,fs) = (tag,xs) := Option.some.inj h
      have htag : a = tag := congrArg Prod.fst same
      have hfields : fs = xs := congrArg Prod.snd same
      rw [codeOfCell hc,packOfUnpack t ht,htag,hfields,packNode]

theorem addressCoordinates {q : Nat} {ctx : List Nat} {r k : Nat}
    (h : addressView q = some (ctx,r,k)) :
    q = packNode 3 [pack ctx,r,k] ∧ run addressGood q = 1 ∧
    run rawContext q = pack ctx ∧ run rawResult q = r ∧ run rawLeast q = k := by
  have hu := positiveView h
  have hx := codeOfPositiveNode hu
  have ht : run addressTag q = 3 := literalEvaluation 1 3 (q ::ᵥ nil)
  have hg : run addressGood q = 1 := (nodeArity addressTag 3 q 3 ht).mpr
    ⟨[pack ctx,r,k],hu,rfl⟩
  refine ⟨hx,hg, ?_⟩
  rw [hx]
  let c := pack ctx
  change run rawContext (packNode 3 [c,r,k]) = c ∧ run rawResult (packNode 3 [c,r,k]) = r ∧
    run rawLeast (packNode 3 [c,r,k]) = k
  have outer := (headTailOfCell (cellAt 3 (pack [c,r,k]))).2
  have first : run cellHead (pack [c,r,k]) = c ∧ run cellTail (pack [c,r,k]) = pack [r,k] :=
    headTailOfCell (cellAt c (pack [r,k]))
  have second : run cellHead (pack [r,k]) = r ∧ run cellTail (pack [r,k]) = pack [k] :=
    headTailOfCell (cellAt r (pack [k]))
  have third : run cellHead (pack [k]) = k := (headTailOfCell (cellAt k (pack []))).1
  change run rawContext (NumberedWindowPairAlgorithm.pair 3 (pack [c,r,k])+1) = c ∧
    run rawResult (NumberedWindowPairAlgorithm.pair 3 (pack [c,r,k])+1) = r ∧
    run rawLeast (NumberedWindowPairAlgorithm.pair 3 (pack [c,r,k])+1) = k
  exact ⟨by simp only [rawContext,field,cursor,applyValue,outer,first.1],
    by simp only [rawResult,field,cursor,applyValue,outer,first.2,second.1],
    by simp only [rawLeast,field,cursor,applyValue,outer,first.2,second.2,third]⟩

theorem chosenArrow (r : Nat) : chosenCell r = arrowView r := by
  cases r with
  | zero => exact allInput.1
  | succ r => exact allInput.2 r

theorem arrowMissing {q r : Nat} (hr : run rawResult q = r) (ha : arrowView r = none) :
    run arrowGood q ≠ 1 := by
  rw [arrowGood,applyValue,hr]
  exact noFlagOfNone ((chosenArrow r).trans ha)

theorem exactCoordinates : ExactOriginalAddressArrowCoordinates := by
  intro q ctx r k dom cod hv ha
  obtain ⟨hq,hg,hctx,hr,hk⟩ := addressCoordinates hv
  have found : chosenCell r = some (dom,cod) := (chosenArrow r).trans ha
  obtain ⟨hdom,hcod⟩ := headTailOfCell found
  exact ⟨hq,hg,by rw [arrowGood,applyValue,hr,flagOfCell found],hctx,hr,hk,
    by rw [rawDomain,applyValue,hr,hdom], by rw [rawCodomain,applyValue,hr,hcod]⟩

#print axioms exactCoordinates

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
