import LogicLineages.PersistentMarking.MarkedFamilyCoherence
namespace LogicLineages.PersistentMarking.MarkedFamilyLattice
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

def le (E : Environment) (heads : List Head) (a b : Code) : Bool :=
  (parameters E heads).all fun p =>
    match MarkedFamilyCoding.output E heads a p,MarkedFamilyCoding.output E heads b p with
    | some x,some y => (descriptor E p.2.1).le p.2.2.1 x y
    | _,_ => false

def SemanticLE (E : Environment) (heads : List Head) (v w : Family) : Prop :=
  ∀ p, MarkedFamilyParameters.Valid E heads p →
    (descriptor E p.2.1).le p.2.2.1 (v p) (w p) = true

def aggregate (meet : Bool) (E : Environment) (heads : List Head) (cs : List Code) : Family :=
  fun p => if meet then (descriptor E p.2.1).meet p.2.2.1 (cs.map (fun c => MarkedFamilyCoding.decode E heads c p))
    else (descriptor E p.2.1).join p.2.2.1 (cs.map (fun c => MarkedFamilyCoding.decode E heads c p))

def combine (meet : Bool) (E : Environment) (heads : List Head) (cs : List Code) : Code :=
  (MarkedFamilyCoding.encode E heads (aggregate meet E heads cs)).getD []

def join (E : Environment) (heads : List Head) (cs : List Code) : Code := combine false E heads cs
def meet (E : Environment) (heads : List Head) (cs : List Code) : Code := combine true E heads cs
end LogicLineages.PersistentMarking.MarkedFamilyLattice
