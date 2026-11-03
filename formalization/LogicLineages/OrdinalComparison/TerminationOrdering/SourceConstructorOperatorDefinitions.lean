module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperator
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalTupleBuilder

def markedBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I)
    {P : World I} (a : Inputs I f P) : Bits I τ.val P := fun Q =>
  let aQ := (inputFamily I f).restrict Q.property a
  ⟨true,(fun o => MarkedSelectTest.selectTest M f aQ o.val || MarkedCopyTest.copyTest above M f aQ o.val ||
    MarkedStatTest.statTest M f aQ o.val || MarkedFAbsTest.fAbsTest M f aQ o.val),(fun _ => false)⟩

def markedValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I)
    {P : World I} (a : Inputs I f P) : Value I τ.val P :=
  FunctionalTupleBuilderProof.buildValue M f τ (markedBits above M f τ a) a

/-- The actual source rule operator, prior to proving its coherent-family refinement. -/
def operatorRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) : CoherentConstructorLattice.Raw I :=
  fun f τ _ a => markedValue above M f τ a

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperator
