module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
/-- A genuine object-language new pool member. No decoded external witness. -/
def growthWitness {alpha : Type} (pool before after : OTerm alpha) : Formula alpha :=
  existsOne (graph2 contains (numeral 1) (pool.relabel Sum.inl) (.var (.inr 0)) ⊓
    ((graph2 contains (numeral 1) (before.relabel Sum.inl) (.var (.inr 0))).not ⊓
      graph2 contains (numeral 1) (after.relabel Sum.inl) (.var (.inr 0))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability
