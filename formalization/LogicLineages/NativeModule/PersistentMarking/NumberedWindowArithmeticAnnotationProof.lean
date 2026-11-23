module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAnnotationTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationProof
open NumberedWindowAnnotationAlgorithm NumberedWindowArithmeticAnnotationTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticPair (pair)
open NumberedWindowTypingBits (annotationList)

theorem head (f : Head) : declaration (encodeHead f) = (encodeTy f.result,f.arguments.map encodeTy) := by
  cases f <;> simp [declaration,encodeHead,headParts,arrow,Head.result,Head.arguments,encodeTy,
    ← NumberedWindowActualPairAlgorithmChecks.currentDecoder,← NumberedWindowActualPairAlgorithmChecks.currentPair,pairRound]

theorem headDeclaration : HeadDeclaration := by
  intro n
  unfold headOutput
  rw [NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactNominalHeadGuard n]
  cases h : decodeHead n with
  | none => rfl
  | some f =>
    have he := (NumberedWindowArithmeticAtomCodeChecks.exact_HeadCodec.1 n f).mp h
    simpa only [Option.isSome_some,if_true,Option.map_some,← he] using congrArg some (head f)

private theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier {n i : Nat} (hi : i < n) : (table n)[i]? = some (annotations i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · simp only [table,List.getElem?_append_left (tableLength n ▸ h)]
      exact ih h
    · have he : i = n := by omega
      subst i
      change (table n ++ [annotations n])[n]? = some (annotations n)
      simpa only [tableLength] using (List.getElem?_concat_length (l := table n) (a := annotations n))

private theorem nodeTerm (tag : Nat) (fs : List Nat) :
    (annotations (encodeNode tag fs)).1 = termParts (table (encodeNode tag fs)) tag fs := by
  change NumberedWindowAnnotationAlgorithm.termNext _ _ = _
  simp [NumberedWindowAnnotationAlgorithm.termNext,← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem child (tag : Nat) (fs : List Nat) (x : Nat) (hx : x ∈ fs) :
    (table (encodeNode tag fs))[x]? = some (annotations x) := earlier (nodeBelow tag fs x hx)

private theorem argsCell (q r : Nat) : (annotations (pair q r + 1)).2 =
    (annotations q).1 :: (annotations r).2 := by
  have l := earlier (Nat.lt_succ_of_le (pairBounds q r).1)
  have h := earlier (Nat.lt_succ_of_le (pairBounds q r).2)
  change NumberedWindowAnnotationAlgorithm.argsNext (pair q r + 1) (table (pair q r + 1)) = _
  simp [NumberedWindowAnnotationAlgorithm.argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
    pairRound,List.getD_eq_getElem?_getD,l,h]

mutual
theorem term : ∀ q : NTerm, (annotations (encodeTerm q)).1 = encodeTy q.type
  | .free t x | .bound t x | .bottom t => by
    simp [encodeTerm,nodeTerm,termParts,NTerm.type,List.getD_eq_getElem?_getD]
  | .lam t q => by
    change (annotations (encodeNode 2 [encodeTy t,encodeTerm q])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,term q,NTerm.type,encodeTy,arrow,
      ← NumberedWindowActualPairAlgorithmChecks.currentPair]
  | .ordinary f bs => by
    simp [encodeTerm,nodeTerm,termParts,List.getD_eq_getElem?_getD,head,NTerm.type]
  | .numbered f t k bs es | .auxApp _ t _ _ => by
    simp [encodeTerm,nodeTerm,termParts,List.getD_eq_getElem?_getD,NTerm.type]

theorem args : ∀ qs : NArgs, (annotations (encodeArgs qs)).2 = (annotationList qs).map encodeTy
  | .nil => rfl
  | .cons q qs => by
    change (annotations (pair (encodeTerm q) (encodeArgs qs)+1)).2 = _
    simp [argsCell,term q,args qs,annotationList,NArgs.toList]
end

private theorem guarded {α β} (o : Option α) (x : β) (f : α → β)
    (h : ∀ a, o = some a → x = f a) :
    (if o.isSome then some x else none) = o.map f := by
  cases o with
  | none => rfl
  | some a => exact congrArg some (h a rfl)

theorem decoded : DecodedAnnotations := by
  intro n
  unfold output
  rw [NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards n]
  simp only [NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow]
  apply Prod.ext
  · apply guarded
    intro q h
    rw [← (NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.1 n q).mp h]
    exact term q
  · apply guarded
    intro qs h
    rw [← (NumberedWindowArithmeticTermCodeChecks.exact_ArgsCodec.1 n qs).mp h]
    exact args qs
end LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationProof
