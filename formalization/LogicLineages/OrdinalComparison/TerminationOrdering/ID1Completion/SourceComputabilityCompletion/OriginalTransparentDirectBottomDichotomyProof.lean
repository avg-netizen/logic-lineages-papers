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
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTransparentDirectBottomDichotomy OriginalTransparentDirectBottomDichotomySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem bottomEquality {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (s t typ : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hB : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s))) :
    Nonempty (Derivation body Delta (equal s t)) := by
  have hsource := BottomSourceShapeProof.bottomRecover s typ ht hB
  obtain ⟨he⟩ := valueUnique BottomRepresentative.bottomCode s t (Fin.cons typ Fin.elim0) hsource hb
  exact ⟨by simpa only [equalEqn] using he⟩

theorem atCertificate (source : Program 2) (leaf : Program 4)
    (introLaw : ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
      (s t cert parameter typ : OTerm alpha),
      Nonempty (Derivation body Delta
        ((OriginalTransparentDirectBottom.Premises source s t cert parameter typ).imp
          (graph4 leaf InternalOriginalStepGuard.one s t cert parameter))))
    {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (s t parameter typ cert : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source InternalOriginalStepGuard.one s parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s))) :
    Nonempty (Derivation body Delta (Witness leaf s t parameter)) := by
  have hpre : Nonempty (Derivation body Delta
      (OriginalTransparentDirectBottom.Premises source s t cert parameter typ)) :=
    andIntro hs (andIntro hn (andIntro ht (andIntro hb hc)))
  obtain ⟨hrule⟩ := introLaw body alpha Delta s t cert parameter typ
  obtain ⟨hp⟩ := hpre
  have hleaf : Nonempty (Derivation body Delta (graph4 leaf InternalOriginalStepGuard.one s t cert parameter)) :=
    ⟨Derivation.implicationElimination hrule hp⟩
  exact witnessIntro leaf s t parameter cert (andIntro hc hleaf)

theorem nonbottomWitness (source : Program 2) (leaf : Program 4)
    (introLaw : ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
      (s t cert parameter typ : OTerm alpha),
      Nonempty (Derivation body Delta
        ((OriginalTransparentDirectBottom.Premises source s t cert parameter typ).imp
          (graph4 leaf InternalOriginalStepGuard.one s t cert parameter))))
    {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (s t parameter typ : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source InternalOriginalStepGuard.one s parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not)) :
    Nonempty (Derivation body Delta (Witness leaf s t parameter)) := by
  apply programCases OriginalTransparentDirectBottom.certificateCode (Fin.cons s Fin.elim0) _
  intro beta j Theta cert hj hc
  rw [witnessRename]
  have hc' : Nonempty (Derivation body Theta
      (graph1 OriginalTransparentDirectBottom.certificateCode cert (s.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hc
  have hs' := renameInto hs j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hs'
  simp only [graph1Rename] at ht' hb'
  simp only [BottomRepresentative.bottomGraph,graph1Rename,
    OriginalTypedDecoderInternalAcceptanceUnaryProof.notRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hn'
  exact atCertificate source leaf introLaw (s.relabel j) (t.relabel j) (parameter.relabel j) (typ.relabel j) cert
    hs' ht' hb' hn' hc'

/-- Proof-side logical assembly. The public endpoint supplies its checked
concrete wrapper law, not a new assumption in the frozen contract. -/
theorem assemble (source : Program 2) (leaf : Program 4)
    (introLaw : ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
      (s t cert parameter typ : OTerm alpha),
      Nonempty (Derivation body Delta
        ((OriginalTransparentDirectBottom.Premises source s t cert parameter typ).imp
          (graph4 leaf InternalOriginalStepGuard.one s t cert parameter))))
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter typ : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph2 source InternalOriginalStepGuard.one s parameter ⊓
        (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)).imp
        (Result leaf s t parameter))) := by
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
      obtain ⟨he⟩ := bottomEquality s t typ (withHyp ht B) (withHyp hb B) hB
      exact ⟨orLeft he⟩
    · have hn : Nonempty (Derivation body (B.not :: A :: Delta) B.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hw⟩ := nonbottomWitness source leaf introLaw s t parameter typ
        (withHyp hs B.not) (withHyp ht B.not) (withHyp hb B.not) hn
      exact ⟨orRight hw⟩
  obtain ⟨hout⟩ := hout
  exact ⟨Derivation.implicationIntroduction hout⟩

theorem actualConcreteDirectBottomDichotomy :
    OriginalTransparentDirectBottomDichotomyTargets.ActualConcreteDirectBottomDichotomy := by
  intro H G M W oldStep endpoint window
  exact assemble (OriginalUniverseDecoder.source H G M W)
    (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
      (OriginalTransparentDirectBottom.refined (OriginalUniverseDecoder.source H G M W) oldStep))
    (OriginalTransparentDirectBottomWrapperProof.actualOriginalConcreteDirectBottomClosedLeaf
      H G M W oldStep endpoint window)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyProof.actualConcreteDirectBottomDichotomy
