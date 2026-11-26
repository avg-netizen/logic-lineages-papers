module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAnnotationChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowLexicalDischargeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalProof
open Spine NumberedWindowLexicalAlgorithm NumberedWindowArithmeticLexicalTargets NumberedWindowLexicalDischargeProof
open NumberedWindowSyntax NumberedWindowTypingBits NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticPair (pair)

private theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier {n i : Nat} (hi : i < n) : (table n)[i]? = some (requirements i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · simp only [table,List.getElem?_append_left (tableLength n ▸ h)]
      exact ih h
    · have he : i = n := by omega
      subst i
      change (table n ++ [requirements n])[n]? = some (requirements n)
      simpa only [tableLength] using (List.getElem?_concat_length (l := table n) (a := requirements n))

private theorem nodeTerm (tag : Nat) (fs : List Nat) :
    (requirements (encodeNode tag fs)).1 = termParts (table (encodeNode tag fs)) tag fs := by
  change NumberedWindowLexicalAlgorithm.termNext _ _ = _
  simp [NumberedWindowLexicalAlgorithm.termNext,← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem child (tag : Nat) (fs : List Nat) (x : Nat) (hx : x ∈ fs) :
    (table (encodeNode tag fs))[x]? = some (requirements x) := earlier (nodeBelow tag fs x hx)

private theorem argsCell (q r : Nat) : (requirements (pair q r + 1)).2 =
    join (requirements q).1 (requirements r).2 := by
  have l := earlier (Nat.lt_succ_of_le (pairBounds q r).1)
  have h := earlier (Nat.lt_succ_of_le (pairBounds q r).2)
  change NumberedWindowLexicalAlgorithm.argsNext (pair q r + 1) (table (pair q r + 1)) = _
  simp [NumberedWindowLexicalAlgorithm.argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
    pairRound,List.getD_eq_getElem?_getD,l,h]

private theorem annotatedArrow (s t : Ty) :
    NumberedWindowAnnotationAlgorithm.arrow (encodeTy s) (encodeTy t) = encodeTy (.arrow s t) := rfl

mutual
theorem term : ∀ (q : NTerm) (C : BoundContext),
    holds (codeLookup C) (requirements (encodeTerm q)).1 = termOK C q
  | .free t x,C | .bottom t,C => by
    simp [encodeTerm,nodeTerm,termParts,holds,empty,termOK]
  | .bound t i,C => by
    simp [encodeTerm,nodeTerm,termParts,List.getD_eq_getElem?_getD,holdsSlot,boundEq,termOK]
  | .lam t q,C => by
    change holds (codeLookup C) (requirements (encodeNode 2 [encodeTy t,encodeTerm q])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,holdsBinder,term q,termOK]
  | .ordinary f bs,C => by
    change holds (codeLookup C) (requirements (encodeNode 4 [encodeHead f,encodeArgs bs])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,holdsRestrict,
      NumberedWindowArithmeticAnnotationProof.head,NumberedWindowArithmeticAnnotationProof.args,listEq,args bs,termOK]
  | .numbered f t k bs es,C => by
    change holds (codeLookup C) (requirements (encodeNode 5 [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,holdsRestrict,holdsJoin,
      NumberedWindowArithmeticAnnotationProof.head,NumberedWindowArithmeticAnnotationProof.args,listEq,args bs,args es,
      termOK,Bool.and_assoc]
  | .auxApp s t q a,C => by
    change holds (codeLookup C) (requirements (encodeNode 6 [encodeTy s,encodeTy t,encodeTerm q,encodeTerm a])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,holdsRestrict,holdsJoin,
      NumberedWindowArithmeticAnnotationProof.term,annotatedArrow,codeEq,term q,term a,termOK,Bool.and_assoc]

theorem args : ∀ (qs : NArgs) (C : BoundContext),
    holds (codeLookup C) (requirements (encodeArgs qs)).2 = argsOK C qs
  | .nil,C => rfl
  | .cons q qs,C => by
    change holds (codeLookup C) (requirements (pair (encodeTerm q) (encodeArgs qs)+1)).2 = _
    simp [argsCell,holdsJoin,term q,args qs,argsOK]
end

theorem finiteTyped : ExactFiniteTypedChecker := by
  intro Γ τ n
  have ctx : (fun i => (Γ.map encodeTy)[i]?) = codeLookup (binderLookup Γ) := by
    funext i
    exact List.getElem?_map
  have opt (o : Option NTerm) (h : decodeTerm n = o) :
      (o.isSome && ((NumberedWindowAnnotationAlgorithm.annotations n).1 == encodeTy τ) &&
        holds (codeLookup (binderLookup Γ)) (requirements n).1) = o.any (typedBit (binderLookup Γ) τ) := by
    cases o with
    | none => rfl
    | some q =>
      have he := (NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.1 n q).mp h
      rw [← he,NumberedWindowArithmeticAnnotationProof.term,codeEq,term]
      rfl
  unfold typed
  rw [ctx,NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards]
  exact opt _ rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalProof
