module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxPartsProof
open NumberedWindowSyntax NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode
open NumberedWindowSyntaxAlgorithm NumberedWindowAddressAlgorithm NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticSyntaxAlgorithmTargets

private theorem ty (n : Nat) : typeBit n = (decodeTy n).isSome :=
  NumberedWindowArithmeticAddressAlgorithmChecks.exact_ExactTypeGuard n

private theorem headPart : ∀ tag p, headParts tag p = (decodeHeadParts tag p).isSome
  | 0, 0 | 0, _+1 | 1, 0 | 1, _+1 => by rfl
  | 2, p | 3, p => by simp [headParts, decodeHeadParts, ty]
  | 4, p => by
    simp only [headParts,decodeHeadParts,← NumberedWindowActualPairAlgorithmChecks.currentDecoder]
    cases hd : NumberedWindowArithmeticPair.decode p with
    | none => rfl
    | some q =>
      obtain ⟨a,b⟩ := q
      cases ha : decodeTy a <;> cases hb : decodeTy b <;> simp [ty,ha,hb]
  | 5, p => by simp [headParts,decodeHeadParts,← NumberedWindowActualPairAlgorithmChecks.currentDecoder]
  | _+6, _ => rfl

theorem headGuard : ExactNominalHeadGuard := by
  intro n
  unfold headBit decodeHead
  rw [← NumberedWindowActualPairAlgorithmChecks.currentDecoder]
  cases hn : NumberedWindowArithmeticPair.decode n with
  | none => rfl
  | some p => exact headPart p.1 p.2

theorem termShape (term args : Nat → Bool) (td : Nat → Option NTerm) (ad : Nat → Option NArgs)
    (tag : Nat) (fs : List Nat) (ht : ∀ n ∈ fs, term n = (td n).isSome)
    (ha : ∀ n ∈ fs, args n = (ad n).isSome) :
    termParts term args tag fs = (assemble td ad tag fs).isSome := by
  fun_cases assemble td ad tag fs
  case case1 t x => simp [termParts,assemble,ty]
  case case2 t i => simp [termParts,assemble,ty]
  case case3 t q =>
    have cq := ht q (by simp)
    cases h : decodeTy t <;> cases u : td q <;> simp [termParts,assemble,ty,cq,h,u]
  case case4 t => simp [termParts,assemble,ty]
  case case5 g bs =>
    have cb := ha bs (by simp)
    cases h : decodeHead g <;> cases u : ad bs <;> simp [termParts,assemble,headGuard g,cb,h,u]
  case case6 g t k bs es =>
    have cb := ha bs (by simp)
    have ce := ha es (by simp)
    cases h : decodeHead g <;> cases d : decodeTy t <;> cases b : ad bs <;> cases e : ad es <;>
      simp [termParts,assemble,headGuard g,ty,cb,ce,h,d,b,e]
  case case7 s t q a =>
    have cq := ht q (by simp)
    have ca := ht a (by simp)
    cases l : decodeTy s <;> cases r : decodeTy t <;> cases x : td q <;> cases y : td a <;>
      simp [termParts,assemble,ty,cq,ca,l,r,x,y]
  case case8 =>
    unfold termParts
    split <;> first | rfl | grind

end LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxPartsProof
