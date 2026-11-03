module
public import LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphTargets
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives GuardedQueryGraph

def StepPreservesFrame : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ)
    (q r : State Symbol arity Γ (lambdaDepth t)), GuardedQueryGraph.Frame s t q → Step above q r → GuardedQueryGraph.Frame s t r

def ReachableFrame : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ)
    (mode : Mode) (q : State Symbol arity Γ (lambdaDepth t)),
    Reachable above (GuardedQueryGraph.initial mode s t) q → GuardedQueryGraph.Frame s t q

def FreshOpeningAvailability : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (σ τ : Ty) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ)
    (mode : Mode) (P : PortContext (lambdaDepth t)) (source : Packed Symbol arity (portTypes P++Γ))
    (α β : Ty) (body : MarkedTerm Symbol arity (α::(portTypes P++Γ)) β),
    GuardedQueryGraph.Frame s t (queryAt mode P source ⟨.arrow α β,.lam body⟩) →
    ∃ ordinary : Term Symbol arity (α::(portTypes P++Γ)) β, body=embed ordinary ∧
      (∃ i : Fin (lambdaDepth t),i ∉ P.map Prod.fst) ∧
      ∀ i : Fin (lambdaDepth t),i ∉ P.map Prod.fst →
        (⟨(i,α)::P,β,ordinary⟩ : Observation Symbol arity Γ (lambdaDepth t)) ∈ observations (lambdaDepth t) t

def FunPremisesCovered : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (B : Nat) (P : PortContext B) (f g : Head Symbol)
    (ss : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
    (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
    (matched : List (Packed Symbol arity (portTypes P++Γ))),
    headEquivalent f g → headResult f=headResult g → (argumentList ts).Perm matched →
    WeakMatch Symbol arity above (portTypes P++Γ) (argumentList ss) matched →
    ∀ s t,(s,t) ∈ (argumentList ss).zip matched →
      Weak Symbol arity above (portTypes P++Γ) s t ∧
      Step above (queryAt .weak P ⟨_,.ordinary f ss⟩ ⟨_,.ordinary g ts⟩) (queryAt .weak P s t)

def StatPremisesCovered : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (B : Nat) (P : PortContext B) (f g : Head Symbol)
    (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
    (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g)),
    headEquivalent f g → StrictMultiset Symbol arity above (portTypes P++Γ) (argumentList base) (argumentList ts) →
    ∃ kept retained removed inserted : List (Packed Symbol arity (portTypes P++Γ)),
      (argumentList base).Perm (kept++removed) ∧ (argumentList ts).Perm (retained++inserted) ∧ removed≠[] ∧
      (∀ s t,(s,t) ∈ kept.zip retained → Weak Symbol arity above (portTypes P++Γ) s t ∧
        Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩) (queryAt .weak P s t)) ∧
      (∀ t ∈ inserted,∃ s ∈ removed,Strict Symbol arity above (portTypes P++Γ) s t ∧
        Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩) (queryAt .strict P s t))

def IssuedSelectExecutionsBounded : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ)
    (mode : Mode) (q : State Symbol arity Γ (lambdaDepth t)) (issued : IssuedSelect q)
    (d : OriginalApplicationTrace.Configuration Symbol arity (portTypes q.ports++Γ) q.target.1),
    Reachable above (GuardedQueryGraph.initial mode s t) q → OriginalApplicationTrace.Execution (OriginalApplicationTrace.ofSelect issued.request) d →
    OriginalApplicationTrace.Frame (fun υ => υ ∈ inputTypes s t) (fun h => h ∈ markedHeads (embed s))
      (liftAllowedList (inputNames s t) (portTypes q.ports)) d ∧
    OriginalApplicationTrace.PayloadBounds (fun υ => υ ∈ inputTypes s t) (fun h => h ∈ markedHeads (embed s))
      (liftAllowedList (inputNames s t) (portTypes q.ports)) d

end LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphTargets
