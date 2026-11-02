module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsTargets
open Source Source.SourceTypeSupport Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits

def WorldCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (P : PortContext (budget I)),P ∈ worldList I ↔ ValidPorts (typeSupport I.source ∪ typeSupport I.target) P

def ObservationCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (P : World I) (o : ObservationAt I τ P),
    o.val ∈ observations (budget I) I.target ∧ o.val.ports=P.val ∧ o.val.resultType=τ

def ExhaustiveEnumeration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Bits I τ P),a ∈ enumerateBits I τ P

def WeakeningIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Bits I τ P),weaken (fun _ hp => hp) a=a

def WeakeningComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q R : World I) (h : Extends P Q) (k : Extends Q R) (a : Bits I τ P),
    weaken k (weaken h a)=weaken (fun p hp => k p (h p hp)) a

def WeakeningSuprema : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (S : Set (Bits I τ P)),
    weaken h (sSup S)=sSup (weaken h '' S)

def WeakeningInfima : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (S : Set (Bits I τ P)),
    weaken h (sInf S)=sInf (weaken h '' S)

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsTargets
