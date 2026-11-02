module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingTargets
open Source Source.SourceTypeSupport FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets TypedExtraAppend FullTuplePacking

def TypeClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val), (∀ i,(argumentTag I τ s i).val ∈ types I) ∧ (resultTag I τ s).val ∈ types I

def ExactLength : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val) (P : World I) (v : FullTuple I τ.val s P), (packTuple τ s v).length=s.val.1.length

def ExactEntry : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val) (P : World I) (v : FullTuple I τ.val s P) (i : Fin s.val.1.length), (packTuple τ s v)[i.val]?=some ⟨argumentTag I τ s i,v i⟩

def Membership : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val) (P : World I) (v : FullTuple I τ.val s P) (p : Packed I P), p ∈ packTuple τ s v ↔ ∃ i,p=⟨argumentTag I τ s i,v i⟩

def PointwiseDomination : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val) (P : World I) (v w : FullTuple I τ.val s P), v ≤ w → Dominated (packTuple τ s v) (packTuple τ s w)

def WeakeningMap : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : TypeIndex I) (s : Suffix τ.val) (P Q : World I) (h : Extends P Q) (v : FullTuple I τ.val s P), (packTuple τ s v).map (packedWeaken h)=packTuple τ s (tupleWeaken h v)

end LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingTargets
