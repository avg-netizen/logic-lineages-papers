module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

def ExhaustiveEnumeration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P),a ∈ enumerateValues I τ P

def GroundRoundTrips : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I),
    (∀ a : Value I .ground P,groundFromBits (groundToBits a)=a) ∧
    (∀ b : Bits I .ground P,groundToBits (groundFromBits b)=b)

def GroundOrder : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (a b : Value I .ground P),a ≤ b ↔ groundToBits a ≤ groundToBits b

def WeakeningIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P),RecursiveNaturalDomains.weaken (fun _ hp => hp) a=a

def WeakeningComposition : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q R : World I) (h : Extends P Q) (k : Extends Q R) (a : Value I τ P),
    RecursiveNaturalDomains.weaken k (RecursiveNaturalDomains.weaken h a)=RecursiveNaturalDomains.weaken (fun p hp => k p (h p hp)) a

def ApplicationMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P) (s : Suffix τ)
    (v w : FullTuple I τ s P),v ≤ w → applyValue a s v ≤ applyValue a s w

def ApplicationNaturality : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Value I τ P)
    (s : Suffix τ) (v : FullTuple I τ s P),
    RecursiveNaturalDomains.weaken h (applyValue a s v)=
      applyValue (RecursiveNaturalDomains.weaken h a) s (tupleWeaken h v)

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomainsTargets
