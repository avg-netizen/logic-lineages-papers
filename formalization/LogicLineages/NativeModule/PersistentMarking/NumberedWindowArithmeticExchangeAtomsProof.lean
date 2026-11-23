module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticExchangeAtomsTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsProof
open NumberedWindowArithmeticExchangeAtomsTargets NumberedWindowExchangeAtoms
open NumberedWindowHeadEnumerationTargets NumberedWindowPrimaryExchangeBits NumberedWindowSyntax
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTermCode NumberedWindowArithmeticFields
open NumberedWindowArithmeticTermCodeChecks NumberedWindowArithmeticAtomCodeChecks NumberedWindowLiteralEquality

private theorem codeInj {α} {encode : α → Nat} {decode : Nat → Option α}
    (roundtrip : ∀ a, decode (encode a) = some a) {a b : α} (h : encode a = encode b) : a=b := by
  simpa only [roundtrip,Option.some.injEq] using congrArg decode h

private theorem admitted (S K f) : f ∈ admittedHeads S K ↔ headBit S K f = true :=
  ((NumberedWindowHeadEnumerationChecks.exact_AdmittedHeadEnumeration S K).2 f).trans
    (NumberedWindowHeadEnumerationChecks.exact_HeadBit S K f).symm

theorem headPairs : ExactHeadPairCheck := by
  intro S K f g
  apply Bool.eq_iff_iff.mpr
  simp only [allowed,pairs,List.mem_flatMap,List.mem_map,decide_eq_true_eq,
    headPairBit,Bool.and_eq_true,equivalentHeads,List.mem_filter,Prod.mk.injEq]
  constructor
  · rintro ⟨u,hu,v,⟨hv,rank⟩,hu',hv'⟩
    have uf := codeInj exact_HeadCodec.2.1 hu'
    have vg := codeInj exact_HeadCodec.2.1 hv'
    cases uf
    cases vg
    exact ⟨⟨(admitted S K _).mp hu,(admitted S K _).mp hv⟩,rank⟩
  · rintro ⟨⟨hf,hg⟩,rank⟩
    exact ⟨f,(admitted S K f).mpr hf,g,⟨(admitted S K g).mpr hg,rank⟩,rfl,rfl⟩

private theorem fields : ∀ qs : NArgs, encodeArgs qs = encodeFields (qs.toList.map encodeTerm)
  | .nil => rfl
  | .cons q qs => by simp [encodeArgs,NArgs.toList,encodeFields,fields qs]

theorem encoded : ExactEncodedArguments := by
  intro qs
  rw [← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactOrderedFieldCodec.2,fields]
  exact NumberedWindowArithmeticFieldsProof.fieldsRound _

theorem permutation : ExactLiteralPermutation := by
  intro qs rs
  unfold bag
  rw [encoded,encoded]
  apply Bool.eq_iff_iff.mpr
  letI : DecidableEq NTerm := literalDecEq
  change decide ((qs.toList.map encodeTerm).Perm (rs.toList.map encodeTerm)) = true ↔
    decide (qs.toList.Perm rs.toList) = true
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    let recover (n : Nat) := (decodeTerm n).getD (.bottom .ground)
    have back := h.map recover
    simpa [recover,List.map_map,Function.comp_def,exact_TermCodec.2.1] using back
  · exact fun h => h.map encodeTerm

theorem equality : ExactLiteralEquality := by
  constructor
  · intro q r
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq,NumberedWindowTypingBitsChecks.exact_LiteralTermEquality]
    exact ⟨codeInj exact_TermCodec.2.1,congrArg encodeTerm⟩
  · intro qs rs
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq,NumberedWindowTypingBitsChecks.exact_LiteralArgsEquality]
    exact ⟨codeInj exact_ArgsCodec.2.1,congrArg encodeArgs⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsProof
