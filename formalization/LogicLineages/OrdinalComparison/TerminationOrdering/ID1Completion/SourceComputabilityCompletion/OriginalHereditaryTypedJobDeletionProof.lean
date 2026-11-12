module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDecorationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDeletionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryTypedJobErasureProof OriginalHereditaryTypedJobDecorationProof

theorem deletionClosure {n c : Nat} {arity : Fin n → Nat} (a : Job n)
 (code : Code (Fin n)) (binders tail : List Ty) (index : Nat)
 (ht : CoreTyped arity a.role a.typ (binders ++ tail) code)
 (hi : OriginalRawSyntaxTransport.arityValue (codeNumber a.core.code) ≤ index) :
 ∀ b ∈ decorate c a index (deletionsFrom code binders tail), Typed arity b := by
 induction tail generalizing binders index with
 | nil => simp [deletionsFrom,decorate]
 | cons sigma tail ih =>
   intro b hb
   simp only [deletionsFrom,decorate,List.mem_cons] at hb
   rcases hb with rfl | hb
   · rw [childInherited a index _ hi]
     exact erasedCore a.role a.typ binders tail sigma code ht
   · apply ih (binders ++ [sigma]) (index+1) ?_ (by omega) b hb
     simpa only [List.append_assoc,List.singleton_append] using ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDeletionProof
