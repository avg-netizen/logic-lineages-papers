module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowStatParsingProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowStatMarkProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimitiveWitnessChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowStatReplacementProof
open NumberedWindowStatAlgorithm NumberedWindowStatTargets NumberedWindowStatParsingProof
open NumberedWindowStatMarkProof NumberedWindowPrimitiveWitnessBits
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticRawRootCode

private theorem perm (qs rs : List NTerm) :
    decide ((qs.map encodeTerm).Perm (rs.map encodeTerm)) = permBit qs rs := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,NumberedWindowPrimitiveWitnessChecks.exact_LiteralPermutationBit qs rs]
  constructor
  · intro h
    let read (n : Nat) := (decodeTerm n).getD (.bottom .ground)
    have back := h.map read
    simpa [read,List.map_map,Function.comp_def,exact_TermCodec.2.1] using back
  · exact fun h => h.map encodeTerm

private theorem markLiteral (Q R : NTerm) : mark (encodeTerm Q) (encodeTerm R) = markBit Q R := by
  rw [markExact,exact_TermCodec.2.1 Q,exact_TermCodec.2.1 R]
  rfl

private theorem preservesEmpty (xs : List NTerm) : (xs.map encodeTerm).isEmpty = xs.isEmpty := by
  cases xs <;> rfl

private theorem listsExact (qs rs : NArgs) (p : ReplacementWitness) :
    replacementLists (qs.toList.map encodeTerm) (rs.toList.map encodeTerm) (encodePartition p) =
      replacementBit qs rs p := by
  simp only [replacementLists,encodePartition,← List.map_append,perm,preservesEmpty,
    List.all_map,List.any_map,Function.comp_def,markLiteral,replacementBit]

theorem replacementExact : ExactReplacement := by
  intro q w r
  unfold replacement
  rw [argsExact q,partitionExact w,argsExact r]
  cases decodeArgs q <;> cases decodeReplacement w <;> cases decodeArgs r <;>
    simp [Option.any,listsExact]

end LogicLineages.PersistentMarking.NumberedWindowStatReplacementProof
