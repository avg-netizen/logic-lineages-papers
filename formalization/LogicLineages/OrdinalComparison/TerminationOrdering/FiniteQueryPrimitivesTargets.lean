module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesTargets
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport
open ComparisonFreeVariables FiniteQueryPrimitives

def LiteralHeadCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ) (P : Head Symbol → Prop),
    headsAllowed P q ↔ ∀ h ∈ markedHeads q,P h

def InitialFrame : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (σ τ : Ty) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ),
    SubtypeClosed (fun υ => υ ∈ inputTypes s t) ∧ Frame s t (initial s t)

def EverySelectAttemptClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Γ)
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (τ : Ty)
    (request : SelectAttempt f base extraTypes extras τ),
    SubtypeClosed K → typesAllowed K (.marked f τ base extraTypes extras) →
    headsAllowed P (.marked f τ base extraTypes extras) → Supported (.marked f τ base extraTypes extras) a →
    K request.selectedType ∧ (∀ υ ∈ request.suppliedTypes,K υ) ∧ K τ ∧
    typesAllowed K request.selected ∧ headsAllowed P request.selected ∧ Supported request.selected a ∧
    argumentTypesAllowed K (attemptArguments request) ∧ argumentsAllowed P (attemptArguments request) ∧
    ArgumentsSupported (attemptArguments request) a ∧
    ∀ result, attemptResult request=some result →
      typesAllowed K result ∧ headsAllowed P result ∧ Supported result a

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesTargets
