module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraph
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives

inductive Mode where | weak | strict

structure State (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (B : Nat) where
  mode : Mode
  ports : PortContext B
  source : Packed Symbol arity (portTypes ports++Γ)
  target : Packed Symbol arity (portTypes ports++Γ)

def queryAt {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (mode : Mode) (P : PortContext B) (s t : Packed Symbol arity (portTypes P++Γ)) : State Symbol arity Γ B := ⟨mode,P,s,t⟩

def fromQuery {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (mode : Mode) (q : Query Symbol arity Γ B) : State Symbol arity Γ B :=
  ⟨mode,q.observation.ports,q.source,⟨q.observation.resultType,embed q.observation.body⟩⟩

def initial {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (mode : Mode) (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) : State Symbol arity Γ (lambdaDepth t) :=
  fromQuery mode (FiniteQueryPrimitives.initial s t)

def Frame {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) (q : State Symbol arity Γ (lambdaDepth t)) : Prop :=
  typesAllowed (fun υ => υ ∈ inputTypes s t) q.source.2 ∧
  headsAllowed (fun h => h ∈ markedHeads (embed s)) q.source.2 ∧
  Supported q.source.2 (liftAllowedList (inputNames s t) (portTypes q.ports)) ∧
  ∃ body : Term Symbol arity (portTypes q.ports++Γ) q.target.1,
    q.target.2=embed body ∧ (⟨q.ports,q.target.1,body⟩ : Observation Symbol arity Γ (lambdaDepth t)) ∈ observations (lambdaDepth t) t

inductive Step {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (above : Symbol → Symbol → Prop) : State Symbol arity Γ B → State Symbol arity Γ B → Prop where
  | mark (P : PortContext B) {σ : Ty} (s r : MarkedTerm Symbol arity (portTypes P++Γ) σ)
      (t : Packed Symbol arity (portTypes P++Γ)) : strictMark s=some r →
      Step above (queryAt .strict P ⟨σ,s⟩ t) (queryAt .weak P ⟨σ,r⟩ t)
  | put (P : PortContext B) (f : Head Symbol) (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (t : Packed Symbol arity (portTypes P++Γ)) :
      Step above (queryAt .weak P ⟨_,.ordinary f base⟩ t) (queryAt .weak P ⟨_,.marked f (headResult f) base [] .nil⟩ t)
  | abs (P : PortContext B) (σ τ : Ty) (s t : MarkedTerm Symbol arity (σ::(portTypes P++Γ)) τ)
      (i : Fin B) : i ∉ P.map Prod.fst →
      Step above (queryAt .weak P ⟨.arrow σ τ,.lam s⟩ ⟨.arrow σ τ,.lam t⟩)
        (queryAt .weak ((i,σ)::P) ⟨τ,s⟩ ⟨τ,t⟩)
  | funPair (P : PortContext B) (f g : Head Symbol)
      (ss : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
      (matched : List (Packed Symbol arity (portTypes P++Γ))) (s t : Packed Symbol arity (portTypes P++Γ)) :
      headEquivalent f g → headResult f=headResult g → (argumentList ts).Perm matched →
      (s,t) ∈ (argumentList ss).zip matched →
      Step above (queryAt .weak P ⟨_,.ordinary f ss⟩ ⟨_,.ordinary g ts⟩) (queryAt .weak P s t)
  | select (P : PortContext B) (f : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types) (τ : Ty)
      (request : SelectAttempt f base types extras τ) (r t : MarkedTerm Symbol arity (portTypes P++Γ) τ) :
      attemptResult request=some r →
      Step above (queryAt .weak P ⟨τ,.marked f τ base types extras⟩ ⟨τ,t⟩) (queryAt .weak P ⟨τ,r⟩ ⟨τ,t⟩)
  | fresh (P : PortContext B) (f : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types) (σ τ : Ty)
      (t : MarkedTerm Symbol arity (σ::(portTypes P++Γ)) τ) (i : Fin B) : i ∉ P.map Prod.fst →
      Step above (queryAt .weak P ⟨.arrow σ τ,.marked f (.arrow σ τ) base types extras⟩ ⟨.arrow σ τ,.lam t⟩)
        (queryAt .weak ((i,σ)::P) ⟨τ,openMarked f σ τ base types extras⟩ ⟨τ,t⟩)
  | copy (P : PortContext B) (f g : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
      (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g)) (p : Packed Symbol arity (portTypes P++Γ)) :
      headAbove above f g → p ∈ argumentList ts →
      Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩)
        (queryAt .weak P ⟨p.1,.marked f p.1 base types extras⟩ p)
  | statSide (P : PortContext B) (f g : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
      (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g)) (p : Packed Symbol arity (portTypes P++Γ)) :
      headEquivalent f g → p ∈ argumentList ts →
      Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩)
        (queryAt .weak P ⟨p.1,.marked f p.1 base types extras⟩ p)
  | statRetained (P : PortContext B) (f g : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
      (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
      (kept retained removed inserted : List (Packed Symbol arity (portTypes P++Γ)))
      (s t : Packed Symbol arity (portTypes P++Γ)) :
      headEquivalent f g → (argumentList base).Perm (kept++removed) → (argumentList ts).Perm (retained++inserted) → removed≠[] →
      (s,t) ∈ kept.zip retained →
      Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩) (queryAt .weak P s t)
  | statReplaced (P : PortContext B) (f g : Head Symbol)
      (base : Arguments Symbol arity (portTypes P++Γ) (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity (portTypes P++Γ) types)
      (ts : Arguments Symbol arity (portTypes P++Γ) (headArguments arity g))
      (kept retained removed inserted : List (Packed Symbol arity (portTypes P++Γ)))
      (s t : Packed Symbol arity (portTypes P++Γ)) :
      headEquivalent f g → (argumentList base).Perm (kept++removed) → (argumentList ts).Perm (retained++inserted) → removed≠[] →
      s ∈ removed → t ∈ inserted →
      Step above (queryAt .weak P ⟨_,.marked f (headResult g) base types extras⟩ ⟨_,.ordinary g ts⟩) (queryAt .strict P s t)

inductive Reachable {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (above : Symbol → Symbol → Prop) (root : State Symbol arity Γ B) : State Symbol arity Γ B → Prop where
  | root : Reachable above root root
  | step {q r} : Reachable above root q → Step above q r → Reachable above root r

structure IssuedSelect {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (q : State Symbol arity Γ B) where
  head : Head Symbol
  base : Arguments Symbol arity (portTypes q.ports++Γ) (headArguments arity head)
  extraTypes : List Ty
  extras : Arguments Symbol arity (portTypes q.ports++Γ) extraTypes
  request : SelectAttempt head base extraTypes extras q.target.1
  modeWeak : q.mode=.weak
  sourceEquation : q.source=⟨q.target.1,.marked head q.target.1 base extraTypes extras⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraph
