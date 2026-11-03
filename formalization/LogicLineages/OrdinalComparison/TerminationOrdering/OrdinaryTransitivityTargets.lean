module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTransitivityTargets
open Source Source.SourceMarkedSyntax RecursiveComparison

/-- EXACT ordinary endpoint domain of the paper's pair: all three terms are
actual original source terms embedded into marked syntax. No unrestricted
arbitrary-marked-source transitivity supplier is assumed or claimed. -/
def ActualOriginalTransitivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),Transitive above →
  ∀ (Gamma : List Ty) (tau : Ty) (s t u : Term Symbol arity Gamma tau),
  Weak Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩ →
  Weak Symbol arity above Gamma ⟨tau,embed t⟩ ⟨tau,embed u⟩ →
    Weak Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed u⟩

def ActualStrictWeakCompatibility : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),Transitive above →
  ∀ (Gamma : List Ty) (tau : Ty) (s t u : Term Symbol arity Gamma tau),
  Strict Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩ →
  Weak Symbol arity above Gamma ⟨tau,embed t⟩ ⟨tau,embed u⟩ →
    Strict Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed u⟩

def ActualWeakStrictCompatibility : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),Transitive above →
  ∀ (Gamma : List Ty) (tau : Ty) (s t u : Term Symbol arity Gamma tau),
  Weak Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩ →
  Strict Symbol arity above Gamma ⟨tau,embed t⟩ ⟨tau,embed u⟩ →
    Strict Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed u⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTransitivityTargets
