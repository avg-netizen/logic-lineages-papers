module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Derive the predecessor witness from actual cons, rather than adding a
nonempty-context equality to the public contract. -/
theorem atPair (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed out parameter context extended d gamma predecessor key rank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context extended)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalClassContextObserverSelection.inputs p H G W P).base.oldRepresentative out seed parameter)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing predecessor d gamma))) :
    Nonempty (Derivation body Delta
      (((graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative) key seed parameter).iff
          (graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative) key out parameter)) ⊓
        ((graph2 OriginalClassContextObserver.erasedRank rank seed parameter).iff
          (graph2 OriginalClassContextObserver.erasedRank rank out parameter)))) := by
  obtain ⟨he⟩ := valueUnique InternalListCodec.consCode extended (suc predecessor)
    (Fin.cons d (Fin.cons gamma Fin.elim0)) hc
    (InternalListCodecSupportProof.consValue predecessor d gamma hpair)
  have hne : Nonempty (Derivation body Delta (equal extended (suc predecessor))) :=
    ⟨by simpa only [equalEqn] using he⟩
  exact OriginalClassContextObserverSelectionOutputProof.outputAt p H G W P
    seed out parameter extended predecessor key rank hd
    (pairRight parameter context extended hp) hne hr

theorem outputCons (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed out parameter context extended d gamma key rank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context extended)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalClassContextObserverSelection.inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta
      (((graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative) key seed parameter).iff
          (graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative) key out parameter)) ⊓
        ((graph2 OriginalClassContextObserver.erasedRank rank seed parameter).iff
          (graph2 OriginalClassContextObserver.erasedRank rank out parameter)))) := by
  apply programCases InternalPairing.pairing (Fin.cons d (Fin.cons gamma Fin.elim0)) _
  intro beta j Theta predecessor hj hpair
  simp only [conjunctionRename,OriginalTypedDecoderTransportLogicalProof.iffRename,graph2Rename]
  have hd' := renameInto hd j Theta hj
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [OriginalActiveClassKernel.Domain,conjunctionRename,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hd'
  simp only [graph2Rename] at hp' hc' hr'
  have hpair' : Nonempty (Derivation body Theta
      (graph2 InternalPairing.pairing predecessor (d.relabel j) (gamma.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hpair
  exact atPair p H G W P (seed.relabel j) (out.relabel j) (parameter.relabel j)
    (context.relabel j) (extended.relabel j) (d.relabel j) (gamma.relabel j) predecessor
    (key.relabel j) (rank.relabel j) hd' hp' hc' hr' hpair'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailConsProof
