module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel)
open InternalTagArithmeticSupportProof (refl trans congSuc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original PA successor monotonicity, with the SAME positive gap witness.
No numeric order truth is reflected into a derivation. -/
theorem lessSucc (s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (suc s) (suc t))) := by
  apply InternalOriginalOrderProof.orderCases Gamma s t _ h
  intro β j Delta gap hj he
  simp only [orderRename,sucRelabel]
  obtain ⟨he⟩ := he
  have hg : Nonempty (Derivation body Delta
      (InternalTagArithmeticSyntaxProof.eqn
        (InternalAdditionLawsProof.add (suc (s.relabel j)) (suc gap)) (suc (t.relabel j)))) :=
    ⟨trans (InternalAdditionLawsProof.leftSuccessor (s.relabel j) (suc gap)) (congSuc he)⟩
  exact InternalLessThanProof.lessOfAcceptance (suc (s.relabel j)) (suc (t.relabel j))
    (InternalLessThanSupportProof.acceptOfGap (suc (s.relabel j)) (suc (t.relabel j)) gap hg)

/-- Adding ONE to both actual depths preserves the exact conditional
spine guard, even when the supplied source flag is not known Boolean. -/
theorem conditionalSucc (fm gm nextF nextG flagF flagG depthF depthG : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flagF fm)))
    (hg : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flagG gm)))
    (hpf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nextF flagF (suc depthF))))
    (hpg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing nextG flagG (suc depthG))))
    (hc : Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) fm).imp
        (graph1 InternalUnpair.left (suc z) gm ⊓ ltF depthG depthF)))) :
    Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) nextF).imp
        (graph1 InternalUnpair.left (suc z) nextG ⊓ ltF (suc depthG) (suc depthF)))) := by
  have hif := BottomRepresentativeInternalProof.indicatorIff InternalUnpair.left (suc z)
    nextF fm flagF flagF (pairLeft nextF flagF (suc depthF) hpf) hf ⟨refl flagF⟩
  have hig := BottomRepresentativeInternalProof.indicatorIff InternalUnpair.left (suc z)
    nextG gm flagG flagG (pairLeft nextG flagG (suc depthG) hpg) hg ⟨refl flagG⟩
  let P := graph1 InternalUnpair.left (suc z) nextF
  obtain ⟨hif'⟩ := withHyp hif P
  obtain ⟨hc'⟩ := withHyp hc P
  have hinput : Derivation body (P :: Gamma) (graph1 InternalUnpair.left (suc z) fm) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft hif')
      (Derivation.hypothesis List.mem_cons_self)
  have htarget : Nonempty (Derivation body (P :: Gamma)
      (graph1 InternalUnpair.left (suc z) gm ⊓ ltF depthG depthF)) :=
    ⟨Derivation.implicationElimination hc' hinput⟩
  obtain ⟨hig'⟩ := withHyp hig P
  obtain ⟨ht⟩ := andLeft htarget
  have hout : Derivation body (P :: Gamma) (graph1 InternalUnpair.left (suc z) nextG) :=
    Derivation.implicationElimination (Derivation.conjunctionRight hig') ht
  obtain ⟨hl⟩ := lessSucc depthG depthF (andRight htarget)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hout hl)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationArithmeticProof
