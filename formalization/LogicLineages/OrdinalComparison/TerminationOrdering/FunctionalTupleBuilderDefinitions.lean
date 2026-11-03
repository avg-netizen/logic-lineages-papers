module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullTuplePackingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilder
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets FullTuplePacking CoherentConstructorLattice

def appendInput {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {f : HeadIndex I} {P : World I} (a : Inputs I f P) (xs : List (Packed I P)) : Inputs I f P :=
  ⟨a.1,TypedExtraAppendProof.appendExtras a.2 xs⟩

/-- Exact full tuple component with independent observation bits; no rule bits are inferred here. -/
def buildRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (τ : TypeIndex I) {P : World I}
    (bits : Bits I τ.val P) (a : Inputs I f P) : NaturalTupleLayer.Raw I τ.val (lower I τ.val) P :=
  ⟨bits,fun Q s v => M.val f (resultTag I τ s) Q.val
    (appendInput ((inputFamily I f).restrict Q.property a) (packTuple τ s v))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilder
