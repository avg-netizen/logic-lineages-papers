import LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectProof
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowSelectAlgorithm NumberedWindowOwnerAlgorithm NumberedWindowArithmeticOwnerChecks
open NumberedWindowArithmeticSelectTargets NumberedWindowRawWitnessRootBits
open NumberedWindowArithmeticRootComparisonProof NumberedWindowArithmeticExchangeAtomsChecks
open NumberedWindowArithmeticHeadCode

private theorem slot (qs : NArgs) (i : Nat) :
    qs.toList[i]? = qs.get i := by
  cases qs with
  | nil => rfl
  | cons q qs => cases i with
    | zero => rfl
    | succ i => exact slot qs i

private theorem choose (ex : Bool) (i : Nat) (bs es : NArgs) :
    chosen ex i (encodeArgs bs) (encodeArgs es) =
      ((if ex then es else bs).get i).map encodeTerm := by
  have lookup (xs : NArgs) : ((NumberedWindowFieldAlgorithm.unpack (encodeArgs xs)).bind
      (fun ys => ys[i]?)) = (xs.get i).map encodeTerm := by
    rw [exact_EncodedArguments xs]
    simp [List.getElem?_map,slot]
  cases ex with
  | false => exact lookup bs
  | true => exact lookup es

private theorem annotationGuard (x y : Ty) : (encodeTy x == encodeTy y) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h
    simpa only [NumberedWindowArithmeticAtomCodeChecks.exact_TyCodec.2.1,Option.some.injEq] using
      congrArg decodeTy h
  · exact congrArg encodeTy

private theorem compare (f k bs es domains τ) (q r : NTerm) :
    (((NumberedWindowAnnotationAlgorithm.annotations (encodeTerm q)).1 ==
      (plan (encodeTy τ) (domains.map encodeTy)).1) &&
      applyCopies (encodeHead f) k (encodeArgs bs) (encodeArgs es) (encodeTerm q)
        (plan (encodeTy τ) (domains.map encodeTy)).2 == encodeTerm r) =
    (decide (q.type = Spine.ArrowPrefix domains τ) &&
      resultBit (applications q (ownerCopies f k bs es domains)) r) := by
  rw [NumberedWindowArithmeticAnnotationProof.term,exact_ExactArrowPrefix,annotationGuard]
  by_cases h : q.type = Spine.ArrowPrefix domains τ
  · obtain ⟨out,actual,code,_⟩ := exact_ExactSelectedApplications f k bs es domains τ q h
    simp only [h,decide_true,Bool.true_and,code,actual,resultBit,exact_LiteralEquality.1]
  · simp only [h,decide_false,Bool.false_and]

theorem selectExact : ExactSelectRoot := by
  intro S K ex i domains
  funext a b
  apply onCodes
  intro q r
  cases q <;> simp only [encodeTerm,readNode,Option.any_some,body,List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,reduceCtorEq,
    Bool.false_and,Bool.true_and,rootBit] <;> try rfl
  rename_i f τ k bs es
  cases k with
  | zero => rfl
  | succ k =>
    change (fromOwner ex i (domains.map encodeTy) (encodeTerm r) (encodeHead f) (encodeTy τ)
      (k+1) (encodeArgs bs) (encodeArgs es)) = _
    simp only [fromOwner,choose,Option.any]
    cases h : (if ex then es else bs).get i with
    | none => rfl
    | some x => exact compare f k bs es domains τ x r
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectProof
