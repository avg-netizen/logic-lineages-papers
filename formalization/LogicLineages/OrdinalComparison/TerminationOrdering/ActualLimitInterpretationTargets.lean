module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationTargets
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalTupleBuilder SourceConstructorOperator SourceConstructorIteration

def SourceBitEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (Q : Future P), ((layerView I τ.val P ((limit I above).val f τ P a)).val.1 Q).1=true ∧ ∀ o : ObservationAt I τ.val Q.val, let aQ := (inputFamily I f).restrict Q.property a; ((layerView I τ.val P ((limit I above).val f τ P a)).val.1 Q).2.1 o=(MarkedSelectTest.selectTest (limit I above) f aQ o.val || MarkedCopyTest.copyTest above (limit I above) f aQ o.val || MarkedStatTest.statTest (limit I above) f aQ o.val || MarkedFAbsTest.fAbsTest (limit I above) f aQ o.val) ∧ ((layerView I τ.val P ((limit I above).val f τ P a)).val.1 Q).2.2 o=false

def FullTupleEquation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (Q : Future P) (s : Suffix τ.val) (v : FullTuple I τ.val s Q.val), (layerView I τ.val P ((limit I above).val f τ P a)).val.2 Q s v=(limit I above).val f (FullTuplePacking.resultTag I τ s) Q.val (appendInput ((inputFamily I f).restrict Q.property a) (FullTuplePacking.packTuple τ s v))

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationTargets
