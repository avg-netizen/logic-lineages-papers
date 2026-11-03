module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationTargets
open Source Source.SourceSpecialApplication Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains FullListValueApplication

def EmptyIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P) (v : Values I [] P),applyFull [] τ a v=a

def NonemptyCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (types : List Ty) (τ : Ty) (P : World I) (hne : types ≠ []) (a : Value I (arrows types τ) P) (v : Values I types P),applyFull types τ a v=applyValue a (fullSuffix types τ hne) v

def TypeTransport : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (σ : Ty) (types : List Ty) (τ : Ty) (P : World I) (a : Value I σ P) (v : Values I types P) (h : σ=arrows types τ),applyWith a types τ v h=applyFull types τ (Eq.mp (congrArg (fun υ => Value I υ P) h) a) v

def JointMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (types : List Ty) (τ : Ty) (P : World I) (a b : Value I (arrows types τ) P) (v w : Values I types P),a ≤ b → v ≤ w → applyFull types τ a v ≤ applyFull types τ b w

def Restriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (types : List Ty) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Value I (arrows types τ) P) (v : Values I types P),RecursiveNaturalDomains.weaken h (applyFull types τ a v)=applyFull types τ (RecursiveNaturalDomains.weaken h a) (weakenValues h v)

def Bottom : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (types : List Ty) (τ : Ty) (P : World I) (v : Values I types P),applyFull types τ (ExecutableDomainBottom.bottomValue I (arrows types τ) P) v=ExecutableDomainBottom.bottomValue I τ P

end LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationTargets
