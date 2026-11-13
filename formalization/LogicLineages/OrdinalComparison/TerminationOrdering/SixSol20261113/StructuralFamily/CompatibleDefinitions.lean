module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Compatible
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains
open CoherentConstructorLattice TypedExtraDownsets FullTuplePacking
/-- Literal constructor-level compatibility at the current world. This adds no
scanner, substitution, fixed-point, or source comparison assumption. -/
def CurrentTupleCompatible {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} (M : Constructors I) : Prop :=
  ∀ (f : HeadIndex I) (sigma : TypeIndex I) (P : World I) (a : Inputs I f P)
    (s : Suffix sigma.val) (v : FullTuple I sigma.val s P),
  applyValue (M.val f sigma P a) s v =
    M.val f (resultTag I sigma s) P
      (FunctionalTupleBuilder.appendInput a (packTuple sigma s v))
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Compatible
