import LogicLineages.PersistentMarking.NumberedWindowRawContextTargets
import LogicLineages.PersistentMarking.NumberedWindowLiteralEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFocusProof
open NumberedWindowRawContextAlgorithm NumberedWindowRawContextTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowRawWitnessBits NumberedWindowLiteralEquality
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode NumberedWindowArithmeticAtomCodeChecks
open NumberedWindowArithmeticTermCodeChecks NumberedWindowArithmeticCodecLaws

private theorem bitEq {α} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by apply Bool.eq_iff_iff.mpr; simp

theorem typeInject : Function.Injective encodeTy := by
  intro a b h
  have hd := exact_TyCodec.2.1 a
  rw [h,exact_TyCodec.2.1 b] at hd
  exact (Option.some.inj hd).symm

theorem headInject : Function.Injective encodeHead := by
  intro a b h
  have hd := exact_HeadCodec.2.1 a
  rw [h,exact_HeadCodec.2.1 b] at hd
  exact (Option.some.inj hd).symm

private theorem termInject : Function.Injective encodeTerm := by
  intro a b h
  have hd := exact_TermCodec.2.1 a
  rw [h,exact_TermCodec.2.1 b] at hd
  exact (Option.some.inj hd).symm

private theorem argsInject : Function.Injective encodeArgs := by
  intro a b h
  have hd := exact_ArgsCodec.2.1 a
  rw [h,exact_ArgsCodec.2.1 b] at hd
  exact (Option.some.inj hd).symm

theorem typeEq (a b : Ty) : (encodeTy a == encodeTy b) = decide (a = b) := by
  rw [bitEq]; simp [typeInject.eq_iff]

theorem headEq (a b : Head) : (encodeHead a == encodeHead b) = decide (a = b) := by
  rw [bitEq]; simp [headInject.eq_iff]

theorem termEqCode (a b : NTerm) : (encodeTerm a == encodeTerm b) = termEq a b := by
  apply Bool.eq_iff_iff.mpr
  simp [termInject.eq_iff,NumberedWindowLiteralEqualityProof.term a b]

theorem argsEqCode (a b : NArgs) : (encodeArgs a == encodeArgs b) = argsEq a b := by
  apply Bool.eq_iff_iff.mpr
  simp [argsInject.eq_iff,NumberedWindowLiteralEqualityProof.args a b]

theorem natEq (a b : Nat) : (a == b) = decide (a = b) := bitEq a b

private theorem cellOf (a : NTerm) (as : NArgs) :
    cell (encodeArgs (.cons a as)) = some (encodeTerm a,encodeArgs as) := by
  simp [encodeArgs,cell,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]

private theorem skipNone (i : Nat) : skipPrefix i none = none := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

private theorem focusCons (i : Nat) (a b : NTerm) (as bs : NArgs) :
    focus (i+1) (encodeArgs (.cons a as)) (encodeArgs (.cons b bs)) =
      if termEq a b then focus i (encodeArgs as) (encodeArgs bs) else none := by
  unfold focus
  simp only [skipPrefix,skipPair,Option.bind_eq_bind,Option.bind_some,cellOf,termEqCode]
  cases termEq a b <;> simp [skipNone]

theorem exactFocus : ExactFocus := by
  intro i qs rs test testCode h
  induction i generalizing qs rs with
  | zero =>
    cases qs <;> cases rs
    · simp [focus,skipPrefix,cell,encodeArgs,argsAtBit]
    · simp [focus,skipPrefix,cell,encodeArgs,argsAtBit]
    · simp [focus,skipPrefix,cellOf,cell,encodeArgs,argsAtBit]
    · rename_i a as b bs
      simp only [focus,skipPrefix,Option.bind_eq_bind,Option.bind_some,cellOf,argsEqCode,argsAtBit]
      cases ht : argsEq as bs <;> simp [ht,h,Option.any]
  | succ i ih =>
    cases qs <;> cases rs
    · simp [focus,skipPrefix,skipPair,cell,encodeArgs,skipNone,argsAtBit]
    · simp [focus,skipPrefix,skipPair,cell,encodeArgs,skipNone,argsAtBit]
    · simp [focus,skipPrefix,skipPair,cellOf,cell,encodeArgs,skipNone,argsAtBit]
    · rename_i a as b bs
      rw [focusCons]
      cases hab : termEq a b <;> simp [hab,ih,argsAtBit]

theorem argsAny {α} (o : Option α) (test : α → NTerm → NTerm → Bool)
    (i : Nat) (qs rs : NArgs) :
    o.any (fun c => argsAtBit (test c) i qs rs) =
      argsAtBit (fun q r => o.any (fun c => test c q r)) i qs rs := by
  cases o with
  | none =>
    change false = argsAtBit (fun _ _ => false) i qs rs
    induction i generalizing qs rs with
    | zero => cases qs <;> cases rs <;> simp [argsAtBit]
    | succ i ih => cases qs <;> cases rs <;> simp [argsAtBit,← ih]
  | some c => rfl

end LogicLineages.PersistentMarking.NumberedWindowRawContextFocusProof
