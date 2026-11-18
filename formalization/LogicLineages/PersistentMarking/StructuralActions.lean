import LogicLineages.PersistentMarking.MarkedFamilyLattice
namespace LogicLineages.PersistentMarking.StructuralActions
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode

def fullAction (E : Environment) (σ : Ty) (Γ : Context) (c : Code)
    (ds : List Ty) (τ : Ty) (xs : List Code) : Code :=
  (HereditaryDomainSemantics.decode E σ Γ c).application Γ ds τ xs

def bottom (E : Environment) (σ : Ty) (Γ : Context) : Code := (descriptor E σ).join Γ []

def markedAction (E : Environment) (heads : List Head) (c : Code)
    (p : MarkedFamilyParameters.Parameter) : Option Code := MarkedFamilyCoding.output E heads c p

def insertExtras (E : Environment) (Γ : Context) (es xs : List MarkedExtras.Tagged) : List MarkedExtras.Tagged :=
  MarkedExtras.down E Γ (es ++ xs)
end LogicLineages.PersistentMarking.StructuralActions
