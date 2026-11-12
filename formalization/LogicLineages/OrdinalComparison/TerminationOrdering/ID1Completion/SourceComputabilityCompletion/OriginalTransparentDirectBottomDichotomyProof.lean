module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTransparentDirectBottomDichotomy OriginalTransparentDirectBottomDichotomySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem actualConcreteDirectBottomDichotomy :
    OriginalTransparentDirectBottomDichotomyTargets.ActualConcreteDirectBottomDichotomy := by
  intro H G M W oldStep endpoint window body alpha Delta s t parameter typ
  let source := OriginalUniverseDecoder.source H G M W
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentDirectBottom.refined source oldStep)
  let A := graph2 source InternalOriginalStepGuard.one s parameter ⊓
    (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft h
  have ht := andLeft (andRight h)
  have hb := andRight (andRight h)
  have hout : Nonempty (Derivation body (A :: Delta) (Result leaf s t parameter)) := by
    let B := BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s
    apply formulaCases B
    · have hB : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hsource := BottomSourceShapeProof.bottomRecover s typ (withHyp ht B) hB
      obtain ⟨he⟩ := valueUnique BottomRepresentative.bottomCode s t (Fin.cons typ Fin.elim0)
        hsource (withHyp hb B)
      exact ⟨orLeft (by simpa only [equalEqn] using he)⟩
    · have hn : Nonempty (Derivation body (B.not :: A :: Delta) B.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hs' := withHyp hs B.not
      have ht' := withHyp ht B.not
      have hb' := withHyp hb B.not
      have hw : Nonempty (Derivation body (B.not :: A :: Delta) (Witness leaf s t parameter)) := by
        apply programCases OriginalTransparentDirectBottom.certificateCode (Fin.cons s Fin.elim0) _
        intro beta j Theta cert hj hc
        rw [witnessRename]
        have hs'' := renameInto hs' j Theta hj
        have ht'' := renameInto ht' j Theta hj
        have hb'' := renameInto hb' j Theta hj
        have hn'' := renameInto hn j Theta hj
        simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hs''
        simp only [graph1Rename] at ht'' hb''
        simp only [B,BottomRepresentative.bottomGraph,graph1Rename,
          OriginalTypedDecoderInternalAcceptanceUnaryProof.notRename,
          InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hn''
        have hpre := andIntro hs'' (andIntro hn'' (andIntro ht'' (andIntro hb'' hc)))
        obtain ⟨hrule⟩ := OriginalTransparentDirectBottomWrapperProof.actualOriginalConcreteDirectBottomClosedLeaf
          H G M W oldStep endpoint window body beta Theta (s.relabel j) (t.relabel j) cert (parameter.relabel j) (typ.relabel j)
        obtain ⟨hp⟩ := hpre
        have hleaf : Nonempty (Derivation body Theta
            (graph4 leaf InternalOriginalStepGuard.one (s.relabel j) (t.relabel j) cert (parameter.relabel j))) :=
          ⟨Derivation.implicationElimination hrule hp⟩
        exact witnessIntro leaf (s.relabel j) (t.relabel j) (parameter.relabel j) cert (andIntro hc hleaf)
      obtain ⟨hw⟩ := hw
      exact ⟨orRight hw⟩
  obtain ⟨hout⟩ := hout
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof.actualConcreteDirectBottomDichotomy
