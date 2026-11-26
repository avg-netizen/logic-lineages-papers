module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.PoolProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem primaryTypedCarrier : Targets.InternalPrimaryTypedCarrier := by
  intro n arity B body alpha Delta seed parameter out candidate ht hl hm
  let H := OriginalConcreteHeadSignature.signature n arity
  let G := OriginalDecodedContextValidity.contextGuard n
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalCandidates.candidates n arity H
  let E := TypedPrimaryEdge.edge B
  apply InternalAcceptanceSupportProof.programCases (SeededPrimaryPool.pool T Q) ![seed,parameter] _
  intro beta j Theta pool hj hp
  have hx : (fun i => (![seed,parameter] i).relabel j) = ![seed.relabel j,parameter.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have ht' := renameInto ht j Theta hj
  have hl' := renameInto hl j Theta hj
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hl' hm'
  have hi := SeededPrimaryPool.InternalProof.internalPrimaryCarrier T Q E body beta Theta
    (seed.relabel j) (parameter.relabel j) pool (out.relabel j) ht' hp hl'
  have hmem := PrimaryMonotonicity.InclusionProof.eliminate (out.relabel j) pool (candidate.relabel j) hi hm'
  exact PoolProof.accepted n arity H G (seed.relabel j) (parameter.relabel j) pool (candidate.relabel j) ht' hp hmem
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
