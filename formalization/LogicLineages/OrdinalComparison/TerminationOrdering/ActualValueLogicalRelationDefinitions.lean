module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelation
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment TypedObservationAccess RecursiveComparison ActualComparisonCompleteness

abbrev SyntaxAt {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  MarkedTerm Symbol arity (portTypes P.val++I.context) τ

def argumentAt {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} :
    {types : List Ty} → Arguments Symbol arity Γ types → (i : Fin types.length) → MarkedTerm Symbol arity Γ (types.get i)
  | [],.nil,i => Fin.elim0 i
  | _::_,.cons q qs,i => Fin.cases q (fun j => argumentAt qs j) i

def futureSyntax {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {P Q : World I} (h : Extends P Q) (q : SyntaxAt I τ P) : SyntaxAt I τ Q :=
  renameTerm q (LiteralVariableValue.extendVariables I.context Q.val P.val h)

def BitSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (a : Value I τ P) (q : SyntaxAt I τ P) : Prop :=
  ∀ (Q : World I) (h : Extends P Q) (o : ObservationAt I τ Q),
    (readBit false (weaken h a) o.val=true → Weak Symbol arity above (portTypes Q.val++I.context) ⟨τ,futureSyntax h q⟩ ⟨τ,observedTerm o⟩) ∧
    (readBit true (weaken h a) o.val=true → Strict Symbol arity above (portTypes Q.val++I.context) ⟨τ,futureSyntax h q⟩ ⟨τ,observedTerm o⟩)

abbrev LowerRelation {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) :=
  (υ : Ty) → typeSize υ < typeSize τ → (P : World I) → Value I υ P → SyntaxAt I υ P → Prop

def ApplicationSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (τ : Ty) (R : LowerRelation I τ) (P : World I) (a : Value I τ P) (q : SyntaxAt I τ P) : Prop :=
  ∀ (Q : World I) (h : Extends P Q) (s : Suffix τ) (v : FullTuple I τ s Q)
    (args : Arguments Symbol arity (portTypes Q.val++I.context) s.val.1),
    (∀ i,R (s.val.1.get i) ((Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ _ _ s.property).2 _ (List.get_mem _ _)) Q (v i) (argumentAt args i)) →
    match applyOriginalWith (futureSyntax h q) (fun x => .var x) args
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ _ _).mp s.property).2.symm with
    | none => applyValue (weaken h a) s v=ExecutableDomainBottom.bottomValue I s.val.2 Q
    | some result => R s.val.2 (Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ _ _ s.property).1 Q (applyValue (weaken h a) s v) result

def Related {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (a : Value I τ P) (q : SyntaxAt I τ P) : Prop :=
  BitSound I above τ P a q ∧ ApplicationSound I τ (fun υ _ => Related I above υ) P a q
termination_by typeSize τ
decreasing_by assumption

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelation
