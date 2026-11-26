module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.BackwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.ConcreteBackwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn z sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem closed (n : Nat) (arity : Fin n → Nat)
 (candidate parameter context gamma types carrier sourcePool targetPool : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
 (ha : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
 (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) candidate parameter)))
 (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) targetPool candidate parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) carrier candidate parameter)))
 (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included sourcePool targetPool))) :
 Nonempty (Derivation body Delta (backClosed (OriginalConcreteStructuralEdge.edge n arity) sourcePool carrier parameter)) := by
 apply BackwardProof.introduce (OriginalConcreteStructuralEdge.edge n arity) sourcePool carrier parameter
 intro beta j Theta x y hj hx hy he
 have hp' := renameInto hp j Theta hj
 rw [graph2Rename] at hp'
 have ht' := renameInto ht j Theta hj
 rw [graph1Rename] at ht'
 have ha' := renameInto ha j Theta hj
 rw [WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename] at ha'
 have had' := renameInto had j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at had'
 have hpool' := renameInto hpool j Theta hj
 rw [graph2Rename] at hpool'
 have hl' := renameInto hl j Theta hj
 rw [graph2Rename] at hl'
 have hi' := renameInto hi j Theta hj
 rw [PrimaryMonotonicity.InclusionProof.includedRename] at hi'
 have htarget := PrimaryMonotonicity.InclusionProof.eliminate (sourcePool.relabel j) (targetPool.relabel j) x hi' hx
 have hrev := OriginalInstalledEdgeReversal.Proof.reversal n arity body beta Theta
   x y (parameter.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) hp' ht' ha' he
 exact LengthAlignedPrimary.InternalProof.internalEdgeClosure
   (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
   (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)))
   (OriginalConcreteStructuralEdge.edge n arity) body beta Theta
   (candidate.relabel j) (parameter.relabel j) (targetPool.relabel j) (carrier.relabel j)
   y x had' hpool' hl' hy htarget hrev

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.ConcreteBackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.ConcreteBackwardProof
