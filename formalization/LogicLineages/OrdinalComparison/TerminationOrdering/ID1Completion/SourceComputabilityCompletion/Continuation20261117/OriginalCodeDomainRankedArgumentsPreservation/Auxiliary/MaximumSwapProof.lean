module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumSwapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (eqn suc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum)
open MaximumBaseProof (forward backward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem swap (a b value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 maximum value a b))) :
    Nonempty (Derivation body Delta (graph2 maximum value b a)) := by
  apply programCases maximum ![b,a] _
  intro beta j Theta other hj ho
  have hx : (fun i => (![b,a] i).relabel j) = ![b.relabel j,a.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ho
  rw [graph2Rename]
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  obtain ⟨he⟩ := MaximumAlgebraProof.commutative (a.relabel j) (b.relabel j) (value.relabel j) other hvj ho
  exact outputTransport maximum other (value.relabel j) ![b.relabel j,a.relabel j]
    ⟨InternalTagArithmeticSupportProof.symm he⟩ ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumSwapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumSwapProof
