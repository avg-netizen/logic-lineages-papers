module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalBetaTotalityProof InternalQuotientComparisonProof
open Iteration IterationSyntaxProof SyntaxProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowZero (n : Nat) (arity : Fin n → Nat)
    (pool reached parameter context gamma : OrdinaryArithmetic.Term alpha) :
    Nonempty (Derivation body Delta (AtCount n arity z pool reached parameter gamma context)) := by
  apply introduction body alpha 1 Delta
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
    out z (pool.relabel Sum.inl) (reached.relabel Sum.inl) (parameter.relabel Sum.inl)
  let B : Formula (alpha ⊕ Fin 1) := allAccepted n arity (reached.relabel Sum.inl) (gamma.relabel Sum.inl) (context.relabel Sum.inl)
  obtain ⟨h⟩ := zeroCore (body := body)
    (Delta := B :: A :: Delta.map (fun p => p.relabel Sum.inl)) n arity
    (pool.relabel Sum.inl) (reached.relabel Sum.inl) (parameter.relabel Sum.inl) out
    (context.relabel Sum.inl) (gamma.relabel Sum.inl)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [matrix,zRelabel] using
    Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationProof
