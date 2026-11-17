module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
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

attribute [local irreducible] OriginalConcreteStructuralEdge.edge OriginalConcreteHeadSignature.signature
  OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard SeededPrimaryPool.pool

theorem rowSuccessor (n : Nat) (arity : Fin n → Nat)
    (count seed parameter pool reached boundsRef rootTypeRef : OrdinaryArithmetic.Term alpha)
    (had : Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta
      (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n))
        (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hrow : Nonempty (Derivation body Delta (AtCount n arity count pool reached parameter rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (AtCount n arity (suc count) pool reached parameter rootTypeRef boundsRef)) := by
  apply introduction body alpha 1 Delta
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
  let D := Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  have hj : ∀ p ∈ Delta, p.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ D := by
    intro p hmem; exact List.mem_map.mpr ⟨p,hmem,rfl⟩
  let A := graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
    out (suc (count.relabel Sum.inl)) (pool.relabel Sum.inl)
    (reached.relabel Sum.inl) (parameter.relabel Sum.inl)
  let B : Formula (alpha ⊕ Fin 1) := allAccepted n arity (reached.relabel Sum.inl) (rootTypeRef.relabel Sum.inl) (boundsRef.relabel Sum.inl)
  have had' := renameInto had Sum.inl D hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at had'
  have hpool' := renameInto hpool Sum.inl D hj
  rw [graph2Rename] at hpool'
  have hrow' := renameInto hrow Sum.inl D hj
  rw [atCountRename] at hrow'
  obtain ⟨h⟩ := successorCore n arity (count.relabel Sum.inl) (seed.relabel Sum.inl)
    (parameter.relabel Sum.inl) (pool.relabel Sum.inl) (reached.relabel Sum.inl) out
    (boundsRef.relabel Sum.inl) (rootTypeRef.relabel Sum.inl)
    (withHyp (withHyp had' A) B)
    (withHyp (withHyp hpool' A) B) (withHyp (withHyp hrow' A) B)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [matrix,sucRelabel] using
    Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
