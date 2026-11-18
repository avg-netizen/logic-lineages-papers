import LogicLineages.PersistentMarking.MarkedExtras
import LogicLineages.PersistentMarking.DecisionSourceUniverse
namespace LogicLineages.PersistentMarking.MarkedBaseTuples
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def tuples (E : Environment) (Γ : Context) : List Ty → List (List Code)
  | [] => [[]]
  | σ::ds => ((descriptor E σ).carriers Γ).flatMap (fun c => (tuples E Γ ds).map (c::·))

def headTuples (E : Environment) (Γ : Context) (f : Head) : List (List Code) := tuples E Γ f.arguments

def tupleLe (E : Environment) (Γ : Context) : List Ty → List Code → List Code → Bool
  | [],[],[] => true
  | σ::ds,a::as,b::bs => (descriptor E σ).le Γ a b && tupleLe E Γ ds as bs
  | _,_,_ => false

def restrictTuple (E : Environment) (Γ Θ : Context) (ds : List Ty) (vs : List Code) : List Code :=
  (ds.zip vs).map (fun p => (descriptor E p.1).restrict Γ Θ p.2)
end LogicLineages.PersistentMarking.MarkedBaseTuples
