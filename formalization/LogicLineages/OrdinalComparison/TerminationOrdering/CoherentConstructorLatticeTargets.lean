module
public import LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeTargets
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice

def HeadBaseTypes : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (f : HeadIndex I),∀ τ ∈ headArguments arity f.val,τ ∈ types I

def InputRestrictionCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (f : HeadIndex I) (P Q : World I) (h : Extends P Q) (a : Inputs I f P),
    (∀ i,((inputFamily I f).restrict h a).1 i=RecursiveNaturalDomains.weaken h (a.1 i)) ∧
    (∀ (τ : TypeIndex I) (b : Value I τ.val Q),b ∈ (((inputFamily I f).restrict h a).2 τ).val ↔
      ∃ c ∈ (a.2 τ).val,b ≤ RecursiveNaturalDomains.weaken h c)

def ExhaustiveEnumeration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (M : Constructors I),M ∈ enumerateConstructors I

def SupCoherent : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (S : Set (Constructors I)),CoherentConstructorLattice.Good (CoherentConstructorLattice.supRaw I S)

def InfCoherent : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (S : Set (Constructors I)),CoherentConstructorLattice.Good (CoherentConstructorLattice.infRaw I S)

def SupUniversal : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (S : Set (Constructors I)),IsLUB (Subtype.val '' S) (CoherentConstructorLattice.supRaw I S)

def InfUniversal : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (S : Set (Constructors I)),IsGLB (Subtype.val '' S) (CoherentConstructorLattice.infRaw I S)

def CompleteConstructors : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity),∃ C : CompleteLattice (Constructors I),C.toPartialOrder=constructorOrder I

end LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeTargets
