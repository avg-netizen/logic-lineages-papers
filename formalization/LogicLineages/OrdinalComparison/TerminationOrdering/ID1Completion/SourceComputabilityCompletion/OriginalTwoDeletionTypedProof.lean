module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTypedProof
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding
open OriginalRawSyntaxTransport OriginalTwoDeletion OriginalRawSyntaxTransportTypedSupportProof

theorem castCode {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (h : Gamma = Delta) (q : AuxTerm Symbol arity Gamma tau) :
    termCode (castContext h q) = termCode q := by
  cases h
  rfl

theorem lowerCode {Symbol : Type} {arity : Symbol → Nat}
    (A B Gamma : List Ty) (alpha beta tau : Ty)
    (q : AuxTerm Symbol arity (A ++ alpha :: (B ++ beta :: Gamma)) tau) :
    termCode (lowerFirst A B Gamma alpha beta tau q) =
      eraseCode beta (A.length + B.length) (eraseCode alpha A.length (termCode q)) := by
  simp only [lowerFirst,typedErasure,castCode,List.length_append]

theorem upperCode {Symbol : Type} {arity : Symbol → Nat}
    (A B Gamma : List Ty) (alpha beta tau : Ty)
    (q : AuxTerm Symbol arity (A ++ alpha :: (B ++ beta :: Gamma)) tau) :
    termCode (upperFirst A B Gamma alpha beta tau q) =
      eraseCode alpha A.length (eraseCode beta (A.length + (B.length + 1)) (termCode q)) := by
  simp only [upperFirst,castCode,typedErasure,List.length_append,List.length_cons]

theorem actualTypedCommutation : OriginalTwoDeletionTargets.TypedCommutation := by
  intro Symbol arity A B Gamma alpha beta tau q
  apply NumberedAuxiliaryCodingProof.termCodeInjective Symbol arity ((A ++ B) ++ Gamma) tau
  rw [lowerCode,upperCode]
  have h : A.length < A.length + (B.length + 1) := by omega
  have he := OriginalTwoDeletionRawProof.commute (termCode q) alpha beta A.length
    (A.length + (B.length + 1)) h
  have hi : A.length + (B.length + 1) - 1 = A.length + B.length := by omega
  rw [hi] at he
  exact he.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTypedProof
