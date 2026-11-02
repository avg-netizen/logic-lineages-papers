module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice OrdinaryFunctionalValue

def BasePackingTransport : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P Q : World I) (h : Extends P Q) (b : BaseTuple I f P), (packBase f b).map (packedWeaken h)=packBase f (weakenBase h b)

def FunMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P : World I) (a b : BaseTuple I f P) (o : Observation Symbol arity I.context (budget I)), a ≤ b → funMatch f a o ≤ funMatch f b o

def FunWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P Q : World I) (h : Extends P Q) (b : BaseTuple I f P) (o : Observation Symbol arity I.context (budget I)), (∀ p ∈ Q.val,p ∈ o.ports) → funMatch f (weakenBase h b) o=funMatch f b o

def BitsMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (M N : Constructors I) (P : World I) (a b : BaseTuple I f P) (hr : headResult f.val ∈ types I), M ≤ N → a ≤ b → ordinaryBits M f hr a ≤ ordinaryBits N f hr b

def BitsWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (M : Constructors I) (P Q : World I) (h : Extends P Q) (b : BaseTuple I f P) (hr : headResult f.val ∈ types I), FiniteObservationBits.weaken h (ordinaryBits M f hr b)=ordinaryBits M f hr (weakenBase h b)

def ValueMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (M N : Constructors I) (P : World I) (a b : BaseTuple I f P), M ≤ N → a ≤ b → ordinaryValue M f a ≤ ordinaryValue N f b

def ValueWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (M : Constructors I) (P Q : World I) (h : Extends P Q) (b : BaseTuple I f P), RecursiveNaturalDomains.weaken h (ordinaryValue M f b)=ordinaryValue M f (weakenBase h b)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityTargets
