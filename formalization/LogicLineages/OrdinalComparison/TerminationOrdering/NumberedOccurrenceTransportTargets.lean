module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedTraceContexts NumberedOccurrenceTransport

def ActualArgumentsToList : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma types : List Ty) (args : Arguments Symbol arity Gamma types) (values : AuxArguments Symbol arity Gamma types),
    ArgumentsRepresent Symbol arity n Gamma types args values →
    ListRep n (RecursiveComparison.argumentList args) (argumentList values)

def ActualListToArguments : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma types : List Ty) (args : Arguments Symbol arity Gamma types) (values : List (Packed Symbol arity Gamma)),
    ListRep n (RecursiveComparison.argumentList args) values →
    ∃ target : AuxArguments Symbol arity Gamma types,argumentList target=values ∧
      ArgumentsRepresent Symbol arity n Gamma types args target

def ActualPermutationTransport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma : List Ty) (qs rs : List (OriginalPacked Symbol arity Gamma)) (values : List (Packed Symbol arity Gamma)),
    qs.Perm rs → ListRep n qs values → ∃ target,values.Perm target ∧ ListRep n rs target

def ActualSplitTransport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma : List Ty) (qs rs : List (OriginalPacked Symbol arity Gamma)) (values : List (Packed Symbol arity Gamma)),
    ListRep n (qs++rs) values → ∃ first last,values=first++last ∧ ListRep n qs first ∧ ListRep n rs last

def ActualListBudgetLowering : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n m : Nat),m≤n →
    ∀ (Gamma : List Ty) (qs : List (OriginalPacked Symbol arity Gamma)) (values : List (Packed Symbol arity Gamma)),
    ListRep n qs values → ListRep m qs values

def ActualPointwiseTupleTrace : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma types : List Ty) (args : AuxArguments Symbol arity Gamma types) (values : List (Packed Symbol arity Gamma)),
    PointwiseTrace above (argumentList args) values → ∃ (n : Nat) (target : AuxArguments Symbol arity Gamma types),
      argumentList target=values ∧ TupleTrace Symbol arity above Gamma types n args target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportTargets
