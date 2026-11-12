module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDecorationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryAnnotatedExpansion (annotationValue)

theorem childAnnotation {n c : Nat} (a : Job n) (index : Nat) (s : State (Fin n)) :
 child c a index s =
   ⟨(annotationValue index a.role a.typ (codeNumber a.core.code)).1,
    (annotationValue index a.role a.typ (codeNumber a.core.code)).2,s⟩ := by
 simp only [child,OriginalHereditaryAnnotatedExpansion.decoratedValue,
   OriginalHereditaryAnnotatedExpansion.jobNumber,Nat.unpair_pair]

theorem childInherited {n c : Nat} (a : Job n) (index : Nat) (s : State (Fin n))
 (hi : OriginalRawSyntaxTransport.arityValue (codeNumber a.core.code) ≤ index) :
 child c a index s = ⟨a.role,a.typ,s⟩ := by
 rw [childAnnotation,OriginalHereditaryAnnotatedExpansionTypedProof.deletionInheritance index a.role a.typ _ hi]

theorem decorateAppend {n c : Nat} (a : Job n) (index : Nat) (xs ys : List (State (Fin n))) :
 decorate c a index (xs ++ ys) = decorate c a index xs ++ decorate c a (index + xs.length) ys := by
 induction xs generalizing index with
 | nil => simp [decorate]
 | cons x xs ih =>
   simp only [List.cons_append,decorate,ih,List.length_cons,
     Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDecorationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDecorationProof
