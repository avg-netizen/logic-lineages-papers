module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.ExpansionProof
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

theorem successorCore (n : Nat) (arity : Fin n → Nat)
    (count seed parameter pool reached out boundsRef rootTypeRef : OrdinaryArithmetic.Term alpha)
    (had : Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta
      (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n))
        (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hrow : Nonempty (Derivation body Delta (AtCount n arity count pool reached parameter rootTypeRef boundsRef)))
    (hi : Nonempty (Derivation body Delta
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity)) out (suc count) pool reached parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (allAccepted n arity out rootTypeRef boundsRef)) := by
  let E := OriginalConcreteStructuralEdge.edge n arity
  apply programCases (PrimaryIteration.iterate E)
    (Fin.cons count (Fin.cons pool (Fin.cons reached (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta previous hj hr
  rw [allAcceptedRename]
  simp only [consTermRename,emptyRename] at hr
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at had'
  have hpool' := renameInto hpool j Theta hj
  rw [graph2Rename] at hpool'
  have hrow' := renameInto hrow j Theta hj
  rw [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  simp only [graph4Rename,sucRelabel] at hi'
  have hu' := renameInto hu j Theta hj
  rw [allAcceptedRename] at hu'
  have hexpand := PrimaryIteration.RecursionProof.successorRecover E (count.relabel j) previous
    (out.relabel j) (pool.relabel j) (reached.relabel j) (parameter.relabel j) hr hi'
  have hprevious := rowApply n arity (count.relabel j) (pool.relabel j) (reached.relabel j)
    (parameter.relabel j) previous (boundsRef.relabel j) (rootTypeRef.relabel j) hrow' hr hu'
  exact ExpansionProof.preserved n arity (seed.relabel j) (parameter.relabel j) (pool.relabel j)
    previous (out.relabel j) (boundsRef.relabel j) (rootTypeRef.relabel j) had' hpool' hexpand hprevious

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
