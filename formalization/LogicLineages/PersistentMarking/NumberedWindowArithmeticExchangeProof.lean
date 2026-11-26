import LogicLineages.PersistentMarking.NumberedWindowExchangeTableProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks
import LogicLineages.PersistentMarking.NumberedWindowLexicalDischargeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeProof
open NumberedWindowExchangeAlgorithm NumberedWindowExchangeTableProof NumberedWindowArithmeticExchangeTargets
open NumberedWindowArithmeticExchangeAtomsChecks NumberedWindowArithmeticExchangeAtomsTargets
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowSyntax NumberedWindowPrimaryExchangeBits NumberedWindowArithmeticTermCodeChecks

private theorem headEq (f g : Head) : (encodeHead f == encodeHead g) = decide (f=g) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h
    simpa only [NumberedWindowArithmeticAtomCodeChecks.exact_HeadCodec.2.1,Option.some.injEq]
      using congrArg decodeHead h
  · exact congrArg _

private theorem natEq (i j : Nat) : (i == j) = decide (i=j) := by
  apply Bool.eq_iff_iff.mpr
  simp

private theorem headCode (f g : Head) : encodeHead f = encodeHead g ↔ f=g := by
  simpa only [beq_iff_eq,decide_eq_true_eq] using (Bool.eq_iff_iff.mp (headEq f g))

private theorem tyCode (s t : Ty) : encodeTy s = encodeTy t ↔ s=t :=
  ⟨NumberedWindowLexicalDischargeProof.codeInj,congrArg _⟩

private theorem headPair (S K f g) :
    NumberedWindowExchangeAtoms.allowed (pairs S K) (encodeHead f) (encodeHead g) = headPairBit S K f g :=
  exact_HeadPairCheck S K f g

private theorem bag (qs rs) : NumberedWindowExchangeAtoms.bag (encodeArgs qs) (encodeArgs rs) = permutationBit qs rs :=
  exact_LiteralPermutation qs rs

mutual
theorem term (S K) : ∀ q r : NTerm, (row (pairs S K) (encodeTerm q) (encodeTerm r)).1 = exchangeBit S K q r
  | .free _ _,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq]
  | .bound _ _,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq]
  | .bottom _,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq]
  | .lam _ q,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq,term S K q]
  | .ordinary _ bs,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq,args S K bs]
  | .numbered _ _ _ bs es,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq,args S K bs,args S K es]
  | .auxApp _ _ q a,r => by
    cases r <;> simp [encodeTerm,nodeTerm,parts,exchangeBit,List.getD_eq_getElem?_getD,nodeChildOpt,
      headPair,bag,headCode,tyCode,exact_LiteralEquality.1,exact_LiteralEquality.2,
      NumberedWindowArithmeticAnnotationProof.head,headEq,NumberedWindowLexicalDischargeProof.codeEq,natEq,term S K q,term S K a]

theorem args (S K) : ∀ qs rs : NArgs, (row (pairs S K) (encodeArgs qs) (encodeArgs rs)).2 = argsExchangeBit S K qs rs
  | .nil,rs => by cases rs <;> exact (argsNil _ _).1
  | .cons q qs,.nil => (argsNil _ _).2
  | .cons q qs,.cons r rs => by
    change (row _ (NumberedWindowPairAlgorithm.pair (encodeTerm q) (encodeArgs qs)+1)
      (NumberedWindowPairAlgorithm.pair (encodeTerm r) (encodeArgs rs)+1)).2 = _
    rw [argsCons,term S K q r,args S K qs rs,exact_LiteralEquality.1,exact_LiteralEquality.2]
    rfl
end

private theorem both {α} (x y : Option α) (v : Bool) (b : α → α → Bool)
    (h : ∀ a c, x=some a → y=some c → v=b a c) :
    (x.isSome && y.isSome && v) = x.any (fun a => y.any (b a)) := by
  cases x with
  | none => rfl
  | some a =>
    cases y with
    | none => rfl
    | some c => exact h a c rfl rfl

theorem decoded : DecodedContextualExchange := by
  intro S K a b
  unfold bits
  rw [NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards]
  apply Prod.ext
  · apply both
    intro q r ha hb
    rw [← (exact_TermCodec.1 a q).mp ha,← (exact_TermCodec.1 b r).mp hb]
    exact term S K q r
  · apply both
    intro qs rs ha hb
    rw [← (exact_ArgsCodec.1 a qs).mp ha,← (exact_ArgsCodec.1 b rs).mp hb]
    exact args S K qs rs
end LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeProof
