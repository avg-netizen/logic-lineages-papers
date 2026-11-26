import LogicLineages.PersistentMarking.MarkedFamilyParameters
namespace LogicLineages.PersistentMarking.MarkedFamilyCoding
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters

def lookup : List (Parameter × Nat) → Code → Parameter → Option Nat
  | (p,_)::ps,i::is,q => if parameterEq p q then some i else lookup ps is q
  | _,_,_ => none

def rawCodes (E : Environment) (heads : List Head) : List Code :=
  vectors ((MarkedFamilyParameters.schema E heads).map Prod.snd)

def FitsFamily (E : Environment) (heads : List Head) (c : Code) : Prop :=
  Fits ((MarkedFamilyParameters.schema E heads).map Prod.snd) c

def output (E : Environment) (heads : List Head) (c : Code) (p : Parameter) : Option Code :=
  (lookup (MarkedFamilyParameters.schema E heads) c p).bind fun i =>
    ((descriptor E p.2.1).carriers p.2.2.1)[i]?

abbrev Family := Parameter → Code

def OutputsValid (E : Environment) (heads : List Head) (v : Family) : Prop :=
  ∀ p, MarkedFamilyParameters.Valid E heads p → v p ∈ (descriptor E p.2.1).carriers p.2.2.1

def FamilyEq (E : Environment) (heads : List Head) (v w : Family) : Prop :=
  ∀ p, MarkedFamilyParameters.Valid E heads p → v p = w p

def encode (E : Environment) (heads : List Head) (v : Family) : Option Code :=
  (parameters E heads).mapM fun p => indexOf ((descriptor E p.2.1).carriers p.2.2.1) (v p)

def decode (E : Environment) (heads : List Head) (c : Code) : Family :=
  fun p => (output E heads c p).getD []
end LogicLineages.PersistentMarking.MarkedFamilyCoding
