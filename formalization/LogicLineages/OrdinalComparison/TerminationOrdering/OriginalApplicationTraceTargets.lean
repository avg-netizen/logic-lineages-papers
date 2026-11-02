module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceTargets
open Source Source.SourceMarkedSyntax ComparisonFreeVariables FiniteQueryPrimitives OriginalApplicationTrace

def ExactExecutionEquation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Δ : List Ty) (τ : Ty)
    (c : Configuration Symbol arity Δ τ), evaluate c = match next c with | some d => evaluate d | none => terminal c

def RecursiveStepFrame : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Δ : List Ty) (τ : Ty)
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) (c d : Configuration Symbol arity Δ τ),
    SubtypeClosed K → OriginalApplicationTrace.Frame K P a c → next c=some d → OriginalApplicationTrace.Frame K P a d

def EveryExecutionPayload : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Δ : List Ty) (τ : Ty)
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) (c d : Configuration Symbol arity Δ τ),
    SubtypeClosed K → OriginalApplicationTrace.Frame K P a c → Execution c d →
    OriginalApplicationTrace.Frame K P a d ∧ PayloadBounds K P a d

def EverySelectExecution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty)
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Γ)
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (τ : Ty)
    (request : SelectAttempt f base extraTypes extras τ) (d : Configuration Symbol arity Γ τ),
    SubtypeClosed K → typesAllowed K (.marked f τ base extraTypes extras) →
    headsAllowed P (.marked f τ base extraTypes extras) → Supported (.marked f τ base extraTypes extras) a →
    Execution (ofSelect request) d → OriginalApplicationTrace.Frame K P a d ∧ PayloadBounds K P a d

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceTargets
