module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison RankedTree

def LiteralEmbedding : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (t : Tree Symbol arity Gamma), markedSyntax t=embed (ordinary t)

def LiteralArgumentList : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (n : Nat) (args : Fin n → Tree Symbol arity Gamma),
  argumentList (groundArguments n (fun i => markedSyntax (args i)))=(List.ofFn args).map pack

def GroundSuffix : Prop := ∀ (types : List Ty) (tau : Ty),
  Ty.ground=arrows types tau → types=[] ∧ tau=Ty.ground

/-- Every actual successful Select issued from a bare ranked source has an
EMPTY supplied tuple and returns one literal original source child. This
retains the actual helper equation, not a newly invented zero-argument rule. -/
def ExactSelectExecution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (f : Symbol) (args : Fin (arity f) → Tree Symbol arity Gamma)
    (sigma tau : Ty) (q : MarkedTerm Symbol arity Gamma sigma)
    (types : List Ty) (h : sigma=arrows types tau) (r : MarkedTerm Symbol arity Gamma tau),
  (⟨sigma,q⟩ : Packed Symbol arity Gamma) ∈
    argumentList (groundArguments (arity f) (fun i => markedSyntax (args i))) ++ argumentList (.nil : Arguments Symbol arity Gamma []) →
  applyOriginalWith q (fun v => .var v)
    (selfArguments (.ranked f) (groundArguments (arity f) (fun i => markedSyntax (args i))) [] .nil types) h=some r →
  types=[] ∧ ∃ i : Fin (arity f), (⟨tau,r⟩ : Packed Symbol arity Gamma)=pack (args i)

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeTargets
