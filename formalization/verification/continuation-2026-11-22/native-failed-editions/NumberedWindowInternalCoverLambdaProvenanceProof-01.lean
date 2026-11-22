module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (termParts termNext argsNext syntaxBits table)
open NumberedWindowCoverBoundsAlgorithm (bounds termMeasure)
open NumberedWindowRawExchangeVerticesBoundsTableProof (termBounds previous)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalCoverLambdaProvenanceTargets

private theorem lengthSyntax (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlierSyntax {i n : Nat} (h : i < n) : (table n)[i]? = some (syntaxBits i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases before : i < n
    · simp only [table,List.getElem?_append_left (lengthSyntax n ▸ before)]
      exact ih before
    · have last : i = n := by omega
      subst i
      change (table n ++ [syntaxBits n])[n]? = some (syntaxBits n)
      simpa only [lengthSyntax] using
        (List.getElem?_concat_length (l := table n) (a := syntaxBits n))

private theorem readSyntax {i n : Nat} (h : i < n) :
    (table n).getD i (false,false) = syntaxBits i := by
  rw [List.getD_eq_getElem?_getD,earlierSyntax h]
  rfl

theorem exact_CoverLambdaSourceProvenance : ExactCoverLambdaSourceProvenance := by
  intro raw ty q read
  have smaller := (nodeBounds read).2 q (by simp)
  refine ⟨smaller,?_,?_⟩
  · have atParent : (syntaxBits raw).1 = (typeBit ty && (syntaxBits q).1) := by
      change termNext raw (table raw) = _
      simp [termNext,read,termParts,readSyntax smaller]
    rw [atParent,Bool.and_eq_true]
  · rw [termBounds read]
    change (((NumberedWindowCoverBoundsAlgorithm.table raw).getD q default).1.1 + 1,
      ((NumberedWindowCoverBoundsAlgorithm.table raw).getD q default).1.2) = _
    rw [previous smaller]

theorem exact_CoverLambdaSelectedProvenance : ExactCoverLambdaSelectedProvenance := by
  intro V M vc mc raw ty q read valid
  obtain ⟨small,letter,coordinates⟩ := exact_CoverLambdaSourceProvenance raw ty q read
  have yes : (syntaxBits raw).1 = true := by
    rw [vc raw] at valid
    cases h : (syntaxBits raw).1 <;> simp_all
  obtain ⟨annotation,child⟩ := letter.mp yes
  have vchild : run V q = 1 := by rw [vc q, child] <;> rfl
  have mchild : run M q = Encodable.encode (bounds q).1 := mc q
  have mparent : run M raw = Encodable.encode ((bounds q).1.1+1,(bounds q).1.2) := by
    calc
      run M raw = Encodable.encode (bounds raw).1 := mc raw
      _ = _ := congrArg Encodable.encode coordinates
  exact ⟨small,annotation,vchild,mchild,mparent⟩

#print axioms exact_CoverLambdaSourceProvenance
#print axioms exact_CoverLambdaSelectedProvenance

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceProof
