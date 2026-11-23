module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCoverBoundsTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsProof
open NumberedWindowCoverBoundsAlgorithm NumberedWindowArithmeticCoverBoundsTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowPrimaryCoverSyntax
open NumberedWindowArithmeticPair (pair)

private theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier {n i : Nat} (hi : i < n) : (table n)[i]? = some (bounds i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · simp only [table,List.getElem?_append_left (tableLength n ▸ h)]
      exact ih h
    · have he : i = n := by omega
      subst i
      change (table n ++ [bounds n])[n]? = some (bounds n)
      simpa only [tableLength] using (List.getElem?_concat_length (l := table n) (a := bounds n))

private theorem nodeTerm (tag : Nat) (fs : List Nat) :
    (bounds (encodeNode tag fs)).1 = termMeasure (table (encodeNode tag fs)) tag fs := by
  change NumberedWindowCoverBoundsAlgorithm.termNext _ _ = _
  simp [NumberedWindowCoverBoundsAlgorithm.termNext,← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem child (tag : Nat) (fs : List Nat) (x : Nat) (hx : x ∈ fs) :
    (table (encodeNode tag fs))[x]? = some (bounds x) := earlier (nodeBelow tag fs x hx)

private theorem argsCell (q r : Nat) : (bounds (pair q r + 1)).2 =
    ((bounds q).1.1 + 1 + (bounds r).2.1, max (bounds q).1.2 (bounds r).2.2) := by
  have l := earlier (Nat.lt_succ_of_le (pairBounds q r).1)
  have h := earlier (Nat.lt_succ_of_le (pairBounds q r).2)
  change NumberedWindowCoverBoundsAlgorithm.argsNext (pair q r + 1) (table (pair q r + 1)) = _
  simp [NumberedWindowCoverBoundsAlgorithm.argsNext,
    ← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound,List.getD_eq_getElem?_getD,l,h]

mutual
theorem term : ∀ q : NTerm, (bounds (encodeTerm q)).1 = ((termBounds q).nodes,(termBounds q).numeral)
  | .free t x | .bound t x => by simp [encodeTerm,nodeTerm,termMeasure,termBounds,List.getD_eq_getElem?_getD]
  | .bottom t => by simp [encodeTerm,nodeTerm,termMeasure,termBounds]
  | .lam t q => by
    change (bounds (encodeNode 2 [encodeTy t,encodeTerm q])).1 = _
    simp [nodeTerm,termMeasure,List.getD_eq_getElem?_getD,child,term q,termBounds]
  | .ordinary f bs => by
    change (bounds (encodeNode 4 [encodeHead f,encodeArgs bs])).1 = _
    simp [nodeTerm,termMeasure,List.getD_eq_getElem?_getD,child,args bs,termBounds]
  | .numbered f t k bs es => by
    change (bounds (encodeNode 5 [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es])).1 = _
    simp [nodeTerm,termMeasure,List.getD_eq_getElem?_getD,child,args bs,args es,termBounds]
  | .auxApp s t q a => by
    change (bounds (encodeNode 6 [encodeTy s,encodeTy t,encodeTerm q,encodeTerm a])).1 = _
    simp [nodeTerm,termMeasure,List.getD_eq_getElem?_getD,child,term q,term a,termBounds]

theorem args : ∀ qs : NArgs, (bounds (encodeArgs qs)).2 = ((argsBounds qs).nodes,(argsBounds qs).numeral)
  | .nil => rfl
  | .cons q qs => by
    change (bounds (pair (encodeTerm q) (encodeArgs qs) + 1)).2 = _
    simp [argsCell,term q,args qs,argsBounds]
end

theorem sourceCover : SourceSelectedCover := by
  intro S K n
  unfold NumberedWindowCoverBoundsAlgorithm.cover
  rw [NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards n]
  simp only [NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow]
  cases hn : decodeTerm n with
  | none => rfl
  | some q =>
    have enc := (NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.1 n q).mp hn
    rw [← enc]
    simp only [Option.isSome_some,if_true,term,Option.map_some]
    exact congrArg some (NumberedWindowArithmeticCoverAlgorithmChecks.exact_ExactOriginalCover S K q)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsProof
