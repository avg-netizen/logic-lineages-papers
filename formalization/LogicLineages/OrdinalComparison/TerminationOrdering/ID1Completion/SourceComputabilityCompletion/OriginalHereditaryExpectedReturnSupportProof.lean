module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedUniquenessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
def termJob {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma) : Job n := ⟨0,typeNumber q.1,⟨Gamma,termCode q.2⟩⟩
def argumentJob {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) : Job n := ⟨1,0,⟨Gamma,argumentsCode args⟩⟩

theorem expectedTerm (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) :
 Expected arity R c (termJob q) (settledValue R c ⟨Gamma,q⟩) :=
 Or.inl ⟨q,rfl,rfl,rfl,rfl⟩

theorem expectedArguments (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
 Expected arity R c (argumentJob args) (numbersNumber (argumentValues R c args)) :=
 Or.inr ⟨types,args,rfl,rfl,rfl,rfl⟩

theorem termValue (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) (v : Nat)
 (h : Expected arity R c (termJob q) v) : v = settledValue R c ⟨Gamma,q⟩ :=
 OriginalHereditaryExpectedUniquenessProof.deterministic n arity R c _ _ _ h (expectedTerm R c q)

theorem argumentsValue (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) (v : Nat)
 (h : Expected arity R c (argumentJob args) v) : v = numbersNumber (argumentValues R c args) :=
 OriginalHereditaryExpectedUniquenessProof.deterministic n arity R c _ _ _ h (expectedArguments R c args)

theorem splitAppend {A B : Type} (rel : A → B → Prop) (xs ys : List A) (vs : List B)
 (h : List.Forall₂ rel (xs ++ ys) vs) :
 ∃ left right, vs = left ++ right ∧ List.Forall₂ rel xs left ∧ List.Forall₂ rel ys right := by
 induction xs generalizing vs with
 | nil => exact ⟨[],vs,rfl,.nil,h⟩
 | cons x xs ih =>
   cases h with
   | cons hx ht =>
     obtain ⟨left,right,he,hl,hr⟩ := ih _ ht
     subst he
     exact ⟨_::left,right,rfl,.cons hx hl,hr⟩

theorem relationLength {A B : Type} {rel : A → B → Prop} {xs : List A} {ys : List B}
 (h : List.Forall₂ rel xs ys) : xs.length = ys.length := by
 induction h with
 | nil => rfl
 | cons h ht ih => exact congrArg Nat.succ ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
