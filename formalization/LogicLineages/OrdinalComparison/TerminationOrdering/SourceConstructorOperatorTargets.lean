module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorTargets
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalTupleBuilder SourceConstructorOperator

def SourceBitEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (Q : Future P), ((layerView I τ.val P (operatorRaw above M f τ P a)).val.1 Q).1=true ∧ ∀ o : ObservationAt I τ.val Q.val, let aQ := (inputFamily I f).restrict Q.property a; ((layerView I τ.val P (operatorRaw above M f τ P a)).val.1 Q).2.1 o=(MarkedSelectTest.selectTest M f aQ o.val || MarkedCopyTest.copyTest above M f aQ o.val || MarkedStatTest.statTest M f aQ o.val || MarkedFAbsTest.fAbsTest M f aQ o.val) ∧ ((layerView I τ.val P (operatorRaw above M f τ P a)).val.1 Q).2.2 o=false

def FullTupleEquation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (Q : Future P) (s : Suffix τ.val) (v : FullTuple I τ.val s Q.val), (layerView I τ.val P (operatorRaw above M f τ P a)).val.2 Q s v=M.val f (FullTuplePacking.resultTag I τ s) Q.val (appendInput ((inputFamily I f).restrict Q.property a) (FullTuplePacking.packTuple τ s v))

def NaturalCoherentOutput : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I), CoherentConstructorLattice.Good (operatorRaw above M)

def OperatorMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M N : Constructors I), M ≤ N → operatorRaw above M ≤ operatorRaw above N

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorTargets
