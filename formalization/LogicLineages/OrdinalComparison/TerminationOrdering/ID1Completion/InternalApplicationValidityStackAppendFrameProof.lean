module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack InternalApplicationValidityStackAppend
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationValidityStackAppendTransitionProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendFrameQueryProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The query outputs are original Program graphs; all subsequent branches are internal. -/
theorem frameAtQueries (node leaf : Program 1)
    (frontWork suffix joined initial joinedInitial : OTerm α) (ys : Fin 24 → OTerm α)
    (psi : Formula α)
    (hnz : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (happend : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial (suc z) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing joinedInitial (suc z) joined)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries node leaf i) (ys i)
      (Fin.cons frontWork (Fin.cons suffix Fin.elim0)))))
    (kfail : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) z initial)) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) z joinedInitial)) →
      Nonempty (Derivation body Delta psi))
    (klive : ∀ (Delta : List (Formula α)) (frontNext joinedNext nextState joinedNextState : OTerm α),
      (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 append joinedNext frontNext suffix)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing nextState (suc z) frontNext)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing joinedNextState (suc z) joinedNext)) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) nextState initial)) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) joinedNextState joinedInitial)) →
      Nonempty (Derivation body Delta psi)) : Nonempty (Derivation body Gamma psi) := by
  let xs : Fin 2 → OTerm α := Fin.cons frontWork (Fin.cons suffix Fin.elim0)
  have hhead := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) frontWork xs
    (hq 0) (projectionValue 0 xs)
  have htail := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) frontWork xs
    (hq 1) (projectionValue 0 xs)
  have hjoinTail := binaryRecover append q1 (.projection 1) (ys 2) (ys 1) suffix xs
    (hq 2) (hq 1) (projectionValue 1 xs)
  have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero frontWork (ys 0) (ys 1)
    hnz hhead htail
  have hjcons := consForward frontWork (ys 0) (ys 1) suffix (ys 2) joined hcons hjoinTail happend
  have h3 := unaryRecover InternalUnpair.left q0 (ys 3) (ys 0) xs (hq 3) (hq 0)
  have h4 := unaryRecover InternalUnpair.right q0 (ys 4) (ys 0) xs (hq 4) (hq 0)
  have h5 := unaryRecover InternalUnpair.left q4 (ys 5) (ys 4) xs (hq 5) (hq 4)
  have h6 := unaryRecover InternalUnpair.right q4 (ys 6) (ys 4) xs (hq 6) (hq 4)
  have h7 := unaryRecover InternalUnpair.left q6 (ys 7) (ys 6) xs (hq 7) (hq 6)
  have h8 := unaryRecover InternalUnpair.right q6 (ys 8) (ys 6) xs (hq 8) (hq 6)
  have h9 := unaryRecover InternalUnpair.left q8 (ys 9) (ys 8) xs (hq 9) (hq 8)
  have h10 := unaryRecover InternalUnpair.right q8 (ys 10) (ys 8) xs (hq 10) (hq 8)
  have h11 := unaryRecover leaf q0 (ys 11) (ys 0) xs (hq 11) (hq 0)
  have h12 := unaryRecover node q3 (ys 12) (ys 3) xs (hq 12) (hq 3)
  have h13 := binaryRecover InternalListCodec.consCode q7 q3 (ys 13) (ys 7) (ys 3) xs (hq 13) (hq 7) (hq 3)
  have h14 := binaryRecover InternalPairing.pairing q13 q9 (ys 14) (ys 13) (ys 9) xs (hq 14) (hq 13) (hq 9)
  have h15 := binaryRecover InternalPairing.pairing q7 q10 (ys 15) (ys 7) (ys 10) xs (hq 15) (hq 7) (hq 10)
  have h16 := binaryRecover InternalListCodec.consCode q15 q1 (ys 16) (ys 15) (ys 1) xs (hq 16) (hq 15) (hq 1)
  have h17 := binaryRecover InternalListCodec.consCode q14 q16 (ys 17) (ys 14) (ys 16) xs (hq 17) (hq 14) (hq 16)
  have h18 := binaryRecover InternalListCodec.consCode q15 q2 (ys 18) (ys 15) (ys 2) xs (hq 18) (hq 15) (hq 2)
  have h19 := binaryRecover InternalListCodec.consCode q14 q18 (ys 19) (ys 14) (ys 18) xs (hq 19) (hq 14) (hq 18)
  have h20 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) q1
    (ys 20) (suc z) (ys 1) xs (hq 20) (InternalLessThanSupportProof.oneConstantValue xs) (hq 1)
  have h21 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) q2
    (ys 21) (suc z) (ys 2) xs (hq 21) (InternalLessThanSupportProof.oneConstantValue xs) (hq 2)
  have h22 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) q17
    (ys 22) (suc z) (ys 17) xs (hq 22) (InternalLessThanSupportProof.oneConstantValue xs) (hq 17)
  have h23 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) q19
    (ys 23) (suc z) (ys 19) xs (hq 23) (InternalLessThanSupportProof.oneConstantValue xs) (hq 19)
  have hcur := andLeft (liveConsFields initial frontWork (ys 0) (ys 1) hp hcons)
  have hjcur := andLeft (liveConsFields joinedInitial joined (ys 0) (ys 2) hjp hjcons)
  have fields := headFields initial (ys 0) (ys 3) (ys 4) (ys 5) hcur h3 h4 h5
  have jfields := headFields joinedInitial (ys 0) (ys 3) (ys 4) (ys 5) hjcur h3 h4 h5
  have children := headChildren initial (ys 0) (ys 3) (ys 4) (ys 6) (ys 8) (ys 7)
    (ys 9) (ys 10) (ys 13) (ys 14) (ys 15) hcur h3 h4 h6 h7 h8 h9 h10 h13 h14 h15
  have jchildren := headChildren joinedInitial (ys 0) (ys 3) (ys 4) (ys 6) (ys 8) (ys 7)
    (ys 9) (ys 10) (ys 13) (ys 14) (ys 15) hjcur h3 h4 h6 h7 h8 h9 h10 h13 h14 h15
  have hargAppend := consBackward (ys 16) (ys 15) (ys 1) suffix (ys 2) (ys 18) h16 hjoinTail h18
  have hnextAppend := consBackward (ys 17) (ys 14) (ys 16) suffix (ys 18) (ys 19) h17 hargAppend h19
  apply equalityCases (ys 5) positionTerm psi
  · intro Delta inc htag
    apply equalityCases (ys 11) (suc z) psi
    · intro Theta inc2 hguard
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have tag := tagControl initial (ys 5) z
        (weakenProof (andRight fields) inc3) (weakenProof htag inc2)
      have guard := guardControl leaf current initial (ys 0) (ys 11) z
        (weakenProof hcur inc3) (weakenProof h11 inc3) hguard
      have jtag := tagControl joinedInitial (ys 5) z
        (weakenProof (andRight jfields) inc3) (weakenProof htag inc2)
      have jguard := guardControl leaf current joinedInitial (ys 0) (ys 11) z
        (weakenProof hjcur inc3) (weakenProof h11 inc3) hguard
      apply kfail Theta inc3
      · exact leafReject node leaf initial frontWork (ys 0) (ys 1)
          (weakenProof hp inc3) (weakenProof hcons inc3) tag guard
      · exact leafReject node leaf joinedInitial joined (ys 0) (ys 2)
          (weakenProof hjp inc3) (weakenProof hjcons inc3) jtag jguard
    · intro Theta inc2 hguard
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have tag := tagControl initial (ys 5) z
        (weakenProof (andRight fields) inc3) (weakenProof htag inc2)
      have guard := guardControl leaf current initial (ys 0) (ys 11) (suc z)
        (weakenProof hcur inc3) (weakenProof h11 inc3) hguard
      have jtag := tagControl joinedInitial (ys 5) z
        (weakenProof (andRight jfields) inc3) (weakenProof htag inc2)
      have jguard := guardControl leaf current joinedInitial (ys 0) (ys 11) (suc z)
        (weakenProof hjcur inc3) (weakenProof h11 inc3) hguard
      apply klive Theta (ys 1) (ys 2) (ys 20) (ys 21) inc3
        (weakenProof hjoinTail inc3) (weakenProof h20 inc3) (weakenProof h21 inc3)
      · exact leafPop node leaf initial frontWork (ys 0) (ys 1) (ys 20)
          (weakenProof hp inc3) (weakenProof hcons inc3) tag guard (weakenProof h20 inc3)
      · exact leafPop node leaf joinedInitial joined (ys 0) (ys 2) (ys 21)
          (weakenProof hjp inc3) (weakenProof hjcons inc3) jtag jguard (weakenProof h21 inc3)
  · intro Delta inc htag
    apply equalityCases (ys 12) (suc z) psi
    · intro Theta inc2 hguard
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have tag := tagControl initial (ys 5) (suc z)
        (weakenProof (andRight fields) inc3) (weakenProof htag inc2)
      have guard := guardControl node currentType initial (ys 3) (ys 12) z
        (weakenProof (andLeft fields) inc3) (weakenProof h12 inc3) hguard
      have jtag := tagControl joinedInitial (ys 5) (suc z)
        (weakenProof (andRight jfields) inc3) (weakenProof htag inc2)
      have jguard := guardControl node currentType joinedInitial (ys 3) (ys 12) z
        (weakenProof (andLeft jfields) inc3) (weakenProof h12 inc3) hguard
      apply kfail Theta inc3
      · exact nodeReject node leaf initial frontWork (ys 0) (ys 1)
          (weakenProof hp inc3) (weakenProof hcons inc3) tag guard
      · exact nodeReject node leaf joinedInitial joined (ys 0) (ys 2)
          (weakenProof hjp inc3) (weakenProof hjcons inc3) jtag jguard
    · intro Theta inc2 hguard
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have tag := tagControl initial (ys 5) (suc z)
        (weakenProof (andRight fields) inc3) (weakenProof htag inc2)
      have guard := guardControl node currentType initial (ys 3) (ys 12) (suc z)
        (weakenProof (andLeft fields) inc3) (weakenProof h12 inc3) hguard
      have jtag := tagControl joinedInitial (ys 5) (suc z)
        (weakenProof (andRight jfields) inc3) (weakenProof htag inc2)
      have jguard := guardControl node currentType joinedInitial (ys 3) (ys 12) (suc z)
        (weakenProof (andLeft jfields) inc3) (weakenProof h12 inc3) hguard
      apply klive Theta (ys 17) (ys 19) (ys 22) (ys 23) inc3
        (weakenProof hnextAppend inc3) (weakenProof h22 inc3) (weakenProof h23 inc3)
      · exact nodeExpand node leaf initial frontWork (ys 0) (ys 1) (ys 14) (ys 15)
          (ys 16) (ys 17) (ys 22) (weakenProof hp inc3) (weakenProof hcons inc3) tag guard
          (weakenProof (andLeft children) inc3) (weakenProof (andRight children) inc3)
          (weakenProof h16 inc3) (weakenProof h17 inc3) (weakenProof h22 inc3)
      · exact nodeExpand node leaf joinedInitial joined (ys 0) (ys 2) (ys 14) (ys 15)
          (ys 18) (ys 19) (ys 23) (weakenProof hjp inc3) (weakenProof hjcons inc3) jtag jguard
          (weakenProof (andLeft jchildren) inc3) (weakenProof (andRight jchildren) inc3)
          (weakenProof h18 inc3) (weakenProof h19 inc3) (weakenProof h23 inc3)

/-- One actual transition on a nonempty prefix simulates one transition with a suffix.
Failure is shared; every live successor retains the same suffix through original append. -/
theorem frameCases (node leaf : Program 1)
    (frontWork suffix joined initial joinedInitial : OTerm α) (psi : Formula α)
    (hnz : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (happend : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial (suc z) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing joinedInitial (suc z) joined)))
    (kfail : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) z (initial.relabel j))) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) z (joinedInitial.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j)))
    (klive : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (frontNext joinedNext nextState joinedNextState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing nextState (suc z) frontNext)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing joinedNextState (suc z) joinedNext)) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) nextState (initial.relabel j))) →
      Nonempty (Derivation body Delta (graph1 (transition node leaf) joinedNextState (joinedInitial.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply queryCases (queries node leaf) (Fin.cons frontWork (Fin.cons suffix Fin.elim0)) psi
  intro β j ys Delta hj hq
  have hnz' := renameInto hnz j Delta hj
  have happend' := renameInto happend j Delta hj
  have hp' := renameInto hp j Delta hj
  have hjp' := renameInto hjp j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnz'
  simp only [graph2Rename,sucRelabel,zRelabel] at happend' hp' hjp'
  simp only [consTermRename,emptyRename] at hq
  apply frameAtQueries node leaf (frontWork.relabel j) (suffix.relabel j) (joined.relabel j)
    (initial.relabel j) (joinedInitial.relabel j) ys (psi.relabel j) hnz' happend' hp' hjp' hq
  · intro Theta inc hf hjf
    exact kfail β j Theta (fun p hp => inc _ (hj p hp)) hf hjf
  · intro Theta frontNext joinedNext nextState joinedNextState inc ha hp hjp ht hjt
    exact klive β j Theta frontNext joinedNext nextState joinedNextState
      (fun p hp => inc _ (hj p hp)) ha hp hjp ht hjt

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameProof
