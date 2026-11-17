module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.AtPoolProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z)
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (seed parameter pool out seedType seedRaw boundsRef rootTypeRef : OTerm alpha)
    (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    (hl : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) out seed parameter)))
    (hu : Nonempty (Derivation body Delta (accepted n arity seedType seedRaw rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (allAccepted n arity out rootTypeRef boundsRef)) := by
  let T := (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
  let Q := (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))
  let P := SeededPrimaryPool.pool T Q
  let E := (OriginalConcreteStructuralEdge.edge n arity)
  apply programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta count hj hcount
  rw [allAcceptedRename]
  simp only [consTermRename,emptyRename] at hcount
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at had'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hpool'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hs'
  have hl' := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hl'
  have hu' := renameInto hu j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hu'
  let s := seed.relabel j
  let p := parameter.relabel j
  have hr := successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1])
    (out.relabel j) z ![s,p] had' hl'
  have hi : Nonempty (Derivation body Theta
      (graph4 (PrimaryIteration.run E) (out.relabel j) count (pool.relabel j) s p)) := by
    apply compositionRecover (PrimaryIteration.run E)
      ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1]
      (out.relabel j) ![s,p] ![count,pool.relabel j,s,p] hr
    intro i
    exact Fin.cases hcount (Fin.cases hpool' (Fin.cases (projectionValue 0 ![s,p])
      (Fin.cases (projectionValue 1 ![s,p]) (fun k => Fin.elim0 k)))) i
  exact RunProof.preserved n arity count s p (pool.relabel j) (out.relabel j)
    (seedType.relabel j) (seedRaw.relabel j) (boundsRef.relabel j) (rootTypeRef.relabel j)
    had' hpool' hs' hi hu'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.AtPoolProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.AtPoolProof
