module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets FullTuplePacking CoherentConstructorLattice FunctionalTupleBuilder

def FullTableCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (bits : Bits I τ.val P) (a : Inputs I f P) (Q : Future P) (s : Suffix τ.val) (v : FullTuple I τ.val s Q.val), (buildRaw M f τ bits a).2 Q s v=M.val f (resultTag I τ s) Q.val (appendInput ((inputFamily I f).restrict Q.property a) (packTuple τ s v))

def NaturalTables : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (bits : Bits I τ.val P) (a : Inputs I f P), NaturalTupleLayer.Good (buildRaw M f τ bits a)

def BuilderMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (bits bits' : Bits I τ.val P) (a b : Inputs I f P), M ≤ N → bits ≤ bits' → a ≤ b → buildRaw M f τ bits a ≤ buildRaw N f τ bits' b

def BuilderWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P Q : World I) (h : Extends P Q) (bits : Bits I τ.val P) (a : Inputs I f P), rawWeaken h (buildRaw M f τ bits a)=buildRaw M f τ (FiniteObservationBits.weaken h bits) ((inputFamily I f).restrict h a)

def ActualValueRealization : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (bits : Bits I τ.val P) (a : Inputs I f P), ∃ v : Value I τ.val P,(layerView I τ.val P v).val=buildRaw M f τ bits a

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderTargets
