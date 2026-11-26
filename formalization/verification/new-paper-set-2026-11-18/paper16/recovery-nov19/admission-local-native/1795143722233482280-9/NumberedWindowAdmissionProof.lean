import LogicLineages.PersistentMarking.NumberedWindowAdmissionConstantsProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionProof
open NumberedWindowAdmissionAlgorithm NumberedWindowAdmissionTargets NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticPair (pair)
open NumberedWindowHeadEnumerationTargets (headBit)
open NumberedWindowDomain (support argsSupport heads argsHeads)
open NumberedWindowAdmissionConstantsProof (types)

private theorem tableLength (w : Window) (n : Nat) : (table w n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier (w : Window) {n i : Nat} (hi : i < n) :
    (table w n)[i]? = some (rawBits w i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · simp only [table,List.getElem?_append_left (tableLength w n ▸ h)]
      exact ih h
    · have he : i = n := by omega
      subst i
      change (table w n ++ [rawBits w n])[n]? = some (rawBits w n)
      simpa only [tableLength] using (List.getElem?_concat_length (l := table w n) (a := rawBits w n))

private theorem nodeTerm (w : Window) (tag : Nat) (fs : List Nat) :
    (rawBits w (encodeNode tag fs)).1 = termParts w (table w (encodeNode tag fs)) tag fs := by
  change termNext w _ _ = _
  simp [termNext,← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem child (w : Window) (tag : Nat) (fs : List Nat) (x : Nat) (hx : x ∈ fs) :
    (table w (encodeNode tag fs))[x]? = some (rawBits w x) := earlier w (nodeBelow tag fs x hx)

private theorem argsCell (w : Window) (q r : Nat) : (rawBits w (pair q r + 1)).2 =
    ((rawBits w q).1 && (rawBits w r).2) := by
  have l := earlier w (Nat.lt_succ_of_le (pairBounds q r).1)
  have h := earlier w (Nat.lt_succ_of_le (pairBounds q r).2)
  change argsNext (pair q r + 1) (table w (pair q r + 1)) = _
  simp [argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
    pairRound,List.getD_eq_getElem?_getD,l,h]

private theorem annotatedArrow (s t : Ty) :
    NumberedWindowAnnotationAlgorithm.arrow (encodeTy s) (encodeTy t) = encodeTy (.arrow s t) := rfl

private theorem headSupport {S : Spine.Signature} {K : List Ty} {f : Head}
    (h : headBit S K f = true) : typesIn K (DecisionInventory.declaration f) = true :=
  (Bool.and_eq_true_iff.mp h).2

mutual
theorem term (S : Spine.Signature) (K : List Ty) : ∀ q : NTerm,
    (rawBits (window S K) (encodeTerm q)).1 = termGuard S K q
  | .free t x | .bound t x | .bottom t => by
    simp [encodeTerm,nodeTerm,termParts,types,termGuard,support,heads]
  | .lam t q => by
    change (rawBits _ (encodeNode 2 [encodeTy t,encodeTerm q])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,
      NumberedWindowArithmeticAnnotationProof.term,annotatedArrow,types,term S K q,
      termGuard,support,heads,typesIn,List.all_append,Bool.and_assoc]
  | .ordinary f bs => by
    change (rawBits _ (encodeNode 4 [encodeHead f,encodeArgs bs])).1 = _
    cases hf : headBit S K f with
    | false =>
      simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,args S K bs,
        NumberedWindowAdmissionConstantsProof.heads,termGuard,argsGuard,support,heads,hf]
    | true =>
      have hd : (DecisionInventory.declaration f).all (fun τ => decide (τ ∈ K)) = true :=
        headSupport hf
      simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,args S K bs,
        NumberedWindowAdmissionConstantsProof.heads,termGuard,argsGuard,support,heads,hf,hd,
        List.all_append,typesIn]
  | .numbered f t k bs es => by
    change (rawBits _ (encodeNode 5 [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es])).1 = _
    cases hf : headBit S K f with
    | false =>
      simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,types,
        NumberedWindowAdmissionConstantsProof.heads,args S K bs,args S K es,termGuard,support,heads,hf]
    | true =>
      have hd : (DecisionInventory.declaration f).all (fun τ => decide (τ ∈ K)) = true :=
        headSupport hf
      simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,types,
        NumberedWindowAdmissionConstantsProof.heads,args S K bs,args S K es,termGuard,argsGuard,
        support,heads,hf,hd,typesIn,List.all_append,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
  | .auxApp s t q a => by
    change (rawBits _ (encodeNode 6 [encodeTy s,encodeTy t,encodeTerm q,encodeTerm a])).1 = _
    simp [nodeTerm,termParts,List.getD_eq_getElem?_getD,child,types,term S K q,term S K a,
      termGuard,support,heads,typesIn,List.all_append,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

theorem args (S : Spine.Signature) (K : List Ty) : ∀ qs : NArgs,
    (rawBits (window S K) (encodeArgs qs)).2 = argsGuard S K qs
  | .nil => rfl
  | .cons q qs => by
    change (rawBits _ (pair (encodeTerm q) (encodeArgs qs)+1)).2 = _
    simp [argsCell,term S K q,args S K qs,termGuard,argsGuard,argsSupport,argsHeads,typesIn,
      List.all_append,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
end

theorem literal : LiteralAdmission := by
  constructor
  · intro S K q
    simpa [bits,NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
      NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow,
      NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.2.1] using term S K q
  · intro S K qs
    simpa [bits,NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
      NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow,
      NumberedWindowArithmeticTermCodeChecks.exact_ArgsCodec.2.1] using args S K qs

theorem decoded : DecodedAdmission := by
  intro S K n
  apply Prod.ext
  · cases h : decodeTerm n with
    | none =>
      simp [bits,NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
        NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow,h]
    | some q =>
      have he := (NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.1 n q).mp h
      simpa only [he] using literal.1 S K q
  · cases h : decodeArgs n with
    | none =>
      simp [bits,NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
        NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow,h]
    | some qs =>
      have he := (NumberedWindowArithmeticTermCodeChecks.exact_ArgsCodec.1 n qs).mp h
      simpa only [he] using literal.2 S K qs

end LogicLineages.PersistentMarking.NumberedWindowAdmissionProof
