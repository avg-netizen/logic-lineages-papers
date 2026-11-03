module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView MarkedCopyTest

def GenuineChildGuards : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (o : Observation Symbol arity I.context (budget I)), o ∈ observations (budget I) I.target → ∀ c ∈ plainChildren o,c.resultType ∈ types I

def AllChildrenCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (a : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), allChildrenWeak M f a o=true ↔ ∀ c ∈ plainChildren o,∃ ht : c.resultType ∈ types I,readBit false (M.val f ⟨c.resultType,ht⟩ P a) c=true

def CopyCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (P : World I) (a : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), copyTest above M f a o=true ↔ ∃ (g : Head Symbol) (args : Arguments Symbol arity (portTypes o.ports++I.context) (headArguments arity g)),rootView o.body=some ⟨g,args⟩ ∧ RecursiveComparison.headAbove above f.val g ∧ (∀ c ∈ plainChildren o,∃ ht : c.resultType ∈ types I,readBit false (M.val f ⟨c.resultType,ht⟩ P a) c=true)

def TestMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M N : Constructors I) (f : HeadIndex I) (P : World I) (a b : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), M ≤ N → a ≤ b → copyTest above M f a o ≤ copyTest above N f b o

def CoordinatesMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M N : Constructors I) (f : HeadIndex I) (τ : Ty) (P : World I) (a b : Inputs I f P), M ≤ N → a ≤ b → copyCoordinates above M f τ a ≤ copyCoordinates above N f τ b

def CoordinatesWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Inputs I f P), project h (copyCoordinates above M f τ a)=copyCoordinates above M f τ ((inputFamily I f).restrict h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestTargets
