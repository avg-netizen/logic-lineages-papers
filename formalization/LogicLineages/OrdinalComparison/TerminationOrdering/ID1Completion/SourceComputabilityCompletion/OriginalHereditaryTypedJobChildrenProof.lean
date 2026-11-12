module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDecorationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryTypedJobDecorationProof
open OriginalRawSyntaxTransport (arityValue tagValue)
open OriginalHereditaryAnnotatedExpansion (annotationValue)

theorem termChildrenClosure {n c : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma) :
 ∀ b ∈ decorate c (⟨0,typeNumber q.1,⟨Gamma,termCode q.2⟩⟩ : Job n) 0
   (children Gamma (termCode q.2)), Typed arity b := by
 obtain ⟨tau,q⟩ := q
 cases q <;>
   simp [children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     termCode,codeNumber,typeNumber,Nat.unpair_pair,Nat.add_sub_cancel_left,Typed]
 all_goals first
   | exact CoreTyped.term _
   | exact CoreTyped.arguments _
   | exact ⟨CoreTyped.term _,CoreTyped.term _⟩
   | exact ⟨CoreTyped.arguments _,CoreTyped.arguments _⟩

theorem argumentsChildrenClosure {n c : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) :
 ∀ b ∈ decorate c (⟨1,0,⟨Gamma,argumentsCode args⟩⟩ : Job n) 0
   (children Gamma (argumentsCode args)), Typed arity b := by
 cases args <;>
   simp [children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     argumentsCode,codeNumber,Nat.unpair_pair,Nat.add_sub_cancel_left,Typed]
 exact ⟨CoreTyped.term _,CoreTyped.arguments _⟩

theorem childrenClosure {n c : Nat} {arity : Fin n → Nat} (a : Job n)
 (h : Typed arity a) : ∀ b ∈ decorate c a 0 (children a.core.context a.core.code), Typed arity b := by
 rcases a with ⟨role,typ,Gamma,code⟩
 cases h with
 | term q => exact termChildrenClosure ⟨_,q⟩
 | arguments args => exact argumentsChildrenClosure args

theorem childrenLength {n : Nat} (Gamma : List Ty) (code : Code (Fin n)) :
 (children Gamma code).length = arityValue (codeNumber code) := by
 cases code <;> simp [children,arityValue,tagValue,codeNumber,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
