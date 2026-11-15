module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn suc z)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem unequalZero (out value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out (suc value)))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  obtain ⟨he⟩ := withHyp he (eqn out z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm he) (Derivation.hypothesis List.mem_cons_self)))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
