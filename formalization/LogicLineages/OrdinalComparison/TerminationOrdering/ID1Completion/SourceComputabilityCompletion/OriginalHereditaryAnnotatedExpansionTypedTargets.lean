module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalHereditaryAnnotatedExpansion
/-- Native semantic role/type metadata only, not a validity predicate for
arbitrary annotated jobs. The existing exact forgetting preserves raw jobs. -/
def termAnnotations {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    Packed (Fin n) arity Gamma → List (Nat × Nat)
 | ⟨_,.var _⟩ => []
 | ⟨_,.bottom _⟩ => []
 | ⟨_,@AuxTerm.lam _ _ _ d t q⟩ => [(0,typeNumber t)]
 | ⟨t,@AuxTerm.app _ _ _ d _ f a⟩ => [(0,typeNumber (.arrow d t)),(0,typeNumber d)]
 | ⟨_,.ordinary h base⟩ => [(1,0)]
 | ⟨_,.numbered k h _ base _ extras⟩ => [(1,0),(1,0)]
def argumentAnnotations {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty} :
    AuxArguments (Fin n) arity Gamma types → List (Nat × Nat)
 | .nil => []
 | @AuxArguments.cons _ _ _ tau _ _ _ => [(0,typeNumber tau),(1,0)]
def TermChildren : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  (List.range (OriginalRawSyntaxTransport.arityValue
    (codeNumber (NumberedAuxiliaryCoding.termCode q.2)))).map
      (fun k => annotationValue k 0 (typeNumber q.1)
        (codeNumber (NumberedAuxiliaryCoding.termCode q.2))) = termAnnotations q
def ArgumentsChildren : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (args : AuxArguments (Fin n) arity Gamma types),
  (List.range (OriginalRawSyntaxTransport.arityValue
    (codeNumber (NumberedAuxiliaryCoding.argumentsCode args)))).map
      (fun k => annotationValue k 1 0 (codeNumber (NumberedAuxiliaryCoding.argumentsCode args))) =
      argumentAnnotations args
def DeletionInheritance : Prop := ∀ k role typ raw : Nat,
  OriginalRawSyntaxTransport.arityValue raw ≤ k → annotationValue k role typ raw = (role,typ)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedTargets
