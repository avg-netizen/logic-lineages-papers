module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingTargets
open Source Source.SourceMarkedSyntax RecursiveComparison SourceExtendedMarking

def ActualMarkAlignment : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty)
    (s : MarkedTerm Symbol arity Gamma tau),
  (∀ r,strictMark s=some r → star s=r) ∧ (strictMark s=none → star s=s)

def ActualLeftUnmark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (s t : MarkedTerm Symbol arity Gamma tau),
  SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,star s⟩ ⟨tau,t⟩ →
    SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,s⟩ ⟨tau,t⟩

/-- A real auxiliary derivation transports to the actual total top marking
on both sides. This is not a transitive closure or an assumed strong pair. -/
def ActualMarking : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : Packed Symbol arity Gamma),
  SourceExtendedComparison.Weak Symbol arity above Gamma s t →
    SourceExtendedComparison.Weak Symbol arity above Gamma (starPacked s) (starPacked t)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingTargets
