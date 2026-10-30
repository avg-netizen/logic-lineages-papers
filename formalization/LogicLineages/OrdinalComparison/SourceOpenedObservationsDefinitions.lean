module
public import LogicLineages.OrdinalComparison.SourceLocatedSubtermsDefinitions
public import LogicLineages.OrdinalComparison.SourcePortContextsDefinitions
@[expose] public section
/-! Actual finite opened observations from original typed target subterms.
Context transport is checked literally; depth and assignment tests are explicit.
This is not a recursive-comparison oracle or a finite-closure theorem for it. -/
namespace LogicLineages.OrdinalComparison.Source.SourceOpenedObservations
open SourceTypeSupport SourceLocatedSubterms SourceTypedPorts SourcePortContexts

structure Observation (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (B : Nat) where
  ports : PortContext B
  resultType : Ty
  body : Term Symbol arity (portTypes ports ++ Γ) resultType

def transportContext {Symbol : Type} {arity : Symbol → Nat} {Ξ Ζ : List Ty} {τ : Ty}
    (h : Ξ = Ζ) (t : Term Symbol arity Ξ τ) : Term Symbol arity Ζ τ :=
  Eq.mp (congrArg (fun C => Term Symbol arity C τ) h) t

def openLocated {Symbol : Type} {arity : Symbol → Nat} (Γ : List Ty) {B : Nat}
    (P : PortContext B) (u : LocatedTerm Symbol arity)
    (h : u.ambient = u.binders ++ Γ) (a : PortMap (portTypes P) u.binders) :
    Observation Symbol arity Γ B :=
  ⟨P, u.resultType, (transportContext h u.body).rename (renameWith Γ a)⟩

def observationsAt {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (B : Nat) (t : Term Symbol arity Γ τ) (P : PortContext B) : List (Observation Symbol arity Γ B) :=
  (collect [] t).flatMap fun u =>
    if h : u.ambient = u.binders ++ Γ then
      if P.length + lambdaDepth u.body ≤ B then
        (injectiveMaps (portTypes P) u.binders).map (openLocated Γ P u h)
      else []
    else []

def observations {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (B : Nat) (t : Term Symbol arity Γ τ) : List (Observation Symbol arity Γ B) :=
  (portContexts B (literalTypes t)).flatMap (observationsAt B t)

def plainChildren {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (o : Observation Symbol arity Γ B) : List (Observation Symbol arity Γ B) :=
  match o with
  | ⟨P, _, t⟩ => match t with
    | .var _ => []
    | .lam _ => []
    | .zeroC => []
    | .succC => []
    | .caseC _ => []
    | .recC _ => []
    | .app f a => [⟨P, _, f⟩, ⟨P, _, a⟩]
    | .ranked s args => List.ofFn fun i : Fin (arity s) => ⟨P, .ground, args i⟩

end LogicLineages.OrdinalComparison.Source.SourceOpenedObservations
