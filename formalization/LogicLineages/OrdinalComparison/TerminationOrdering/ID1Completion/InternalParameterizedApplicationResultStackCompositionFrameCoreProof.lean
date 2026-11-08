module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackReturnSupportProof
open InternalApplicationResultStackCompositionFrameSupportProof (extend extendConsForward extendConsBackward)
open InternalApplicationResultStackCompositionFrameConstructorsProof (visitStateAt expandedStateAt conjunctionRejectLeft conjunctionRejectRight)
open InternalParameterizedApplicationResultStackCompositionFrameSupportProof
open InternalParameterizedApplicationResultStackCompositionFrameQueryProof
open InternalApplicationValidityStackAppendListProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof equalityCases)
open InternalApplicationValidityStackAppendRunProof (rightTransport)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalParameterizedApplicationResultStack InternalParameterizedApplicationResultStackWiringProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atQueries (mw mr : Bool) (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (stack results workBackground resultBackground framedStack framedResults state framedState : OTerm α)
    (ys : Fin 44 → OTerm α) (psi : Formula α)
    (hn : Nonempty (Derivation body Gamma (eqn stack z).not))
    (hw : Nonempty (Derivation body Gamma (graph2 (extend mw) framedStack stack workBackground)))
    (hr : Nonempty (Derivation body Gamma (graph2 (extend mr) framedResults results resultBackground)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hfs : Nonempty (Derivation body Gamma (graph2 liveState framedState framedStack framedResults)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries mw mr leaf combine i) (ys i)
      (Fin.cons stack (Fin.cons results (Fin.cons workBackground (Fin.cons resultBackground
        (Fin.cons framedStack (Fin.cons framedResults (Fin.cons parameter Fin.elim0))))))))))
    (kfail : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) z state parameter)) →
      Nonempty (Derivation body Delta psi))
    (klive : ∀ (Delta : List (Formula α)) (nextWork framedNextWork nextResults framedNextResults nextState framedNextState : OTerm α),
      (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (extend mw) framedNextWork nextWork workBackground)) →
      Nonempty (Derivation body Delta (graph2 (extend mr) framedNextResults nextResults resultBackground)) →
      Nonempty (Derivation body Delta (graph2 liveState nextState nextWork nextResults)) →
      Nonempty (Derivation body Delta (graph2 liveState framedNextState framedNextWork framedNextResults)) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) nextState state parameter)) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) framedNextState framedState parameter)) →
      Nonempty (Derivation body Delta psi)) : Nonempty (Derivation body Gamma psi) := by
  let xs : Fin 7 → OTerm α := Fin.cons stack (Fin.cons results (Fin.cons workBackground (Fin.cons resultBackground
    (Fin.cons framedStack (Fin.cons framedResults (Fin.cons parameter Fin.elim0))))))
  have h0 := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) stack xs (hq 0) (projectionValue 0 xs)
  have h1 := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) stack xs (hq 1) (projectionValue 0 xs)
  have h2 := unaryRecover InternalUnpair.left (q0) (ys 2) (ys 0) xs (hq 2) (hq 0)
  have h3 := unaryRecover InternalUnpair.right (q0) (ys 3) (ys 0) xs (hq 3) (hq 0)
  have h4 := unaryRecover InternalUnpair.right (q3) (ys 4) (ys 3) xs (hq 4) (hq 3)
  have h5 := unaryRecover InternalUnpair.left (q3) (ys 5) (ys 3) xs (hq 5) (hq 3)
  have h6 := unaryRecover InternalUnpair.left (q4) (ys 6) (ys 4) xs (hq 6) (hq 4)
  have h7 := unaryRecover InternalUnpair.right (q4) (ys 7) (ys 4) xs (hq 7) (hq 4)
  have h8 := unaryRecover InternalUnpair.left (q7) (ys 8) (ys 7) xs (hq 8) (hq 7)
  have h9 := unaryRecover InternalUnpair.right (q7) (ys 9) (ys 7) xs (hq 9) (hq 7)
  have h10 := unaryRecover InternalUnpair.left (q9) (ys 10) (ys 9) xs (hq 10) (hq 9)
  have h11 := unaryRecover InternalUnpair.right (q9) (ys 11) (ys 9) xs (hq 11) (hq 9)
  have h12 := binaryRecover leaf (q3) (.projection 6) (ys 12) (ys 3) parameter xs (hq 12) (hq 3) (projectionValue 6 xs)
  have h13 := binaryRecover (extend mw) (q1) (.projection 2) (ys 13) (ys 1) workBackground xs (hq 13) (hq 1) (projectionValue 2 xs)
  have h14 := binaryRecover InternalListCodec.consCode (q8) (q5) (ys 14) (ys 8) (ys 5) xs (hq 14) (hq 8) (hq 5)
  have h15 := binaryRecover InternalPairing.pairing (q14) (q10) (ys 15) (ys 14) (ys 10) xs (hq 15) (hq 14) (hq 10)
  have h16 := binaryRecover InternalPairing.pairing (q8) (q11) (ys 16) (ys 8) (ys 11) xs (hq 16) (hq 8) (hq 11)
  have h17 := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 7) (q15) (ys 17) z (ys 15) xs (hq 17) (constantZeroValue xs) (hq 15)
  have h18 := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 7) (q16) (ys 18) z (ys 16) xs (hq 18) (constantZeroValue xs) (hq 16)
  have h19 := binaryRecover InternalPairing.pairing (q8) (q5) (ys 19) (ys 8) (ys 5) xs (hq 19) (hq 8) (hq 5)
  have h20 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 7) (q19) (ys 20) (suc z) (ys 19) xs (hq 20) (InternalLessThanSupportProof.oneConstantValue xs) (hq 19)
  have h21 := binaryRecover InternalListCodec.consCode (q20) (q1) (ys 21) (ys 20) (ys 1) xs (hq 21) (hq 20) (hq 1)
  have h22 := binaryRecover InternalListCodec.consCode (q18) (q21) (ys 22) (ys 18) (ys 21) xs (hq 22) (hq 18) (hq 21)
  have h23 := binaryRecover InternalListCodec.consCode (q17) (q22) (ys 23) (ys 17) (ys 22) xs (hq 23) (hq 17) (hq 22)
  have h24 := binaryRecover InternalListCodec.consCode (q20) (q13 mw) (ys 24) (ys 20) (ys 13) xs (hq 24) (hq 20) (hq 13)
  have h25 := binaryRecover InternalListCodec.consCode (q18) (q24 mw) (ys 25) (ys 18) (ys 24) xs (hq 25) (hq 18) (hq 24)
  have h26 := binaryRecover InternalListCodec.consCode (q17) (q25 mw) (ys 26) (ys 17) (ys 25) xs (hq 26) (hq 17) (hq 25)
  have h27 := binaryRecover InternalListCodec.consCode (q12 leaf) (.projection 1) (ys 27) (ys 12) results xs (hq 27) (hq 12) (projectionValue 1 xs)
  have h28 := binaryRecover InternalListCodec.consCode (q12 leaf) (.projection 5) (ys 28) (ys 12) framedResults xs (hq 28) (hq 12) (projectionValue 5 xs)
  have h29 := binaryRecover liveState (q1) (q27 leaf) (ys 29) (ys 1) (ys 27) xs (hq 29) (hq 1) (hq 27)
  have h30 := binaryRecover liveState (q13 mw) (q28 leaf) (ys 30) (ys 13) (ys 28) xs (hq 30) (hq 13) (hq 28)
  have h31 := binaryRecover liveState (q23) (.projection 1) (ys 31) (ys 23) results xs (hq 31) (hq 23) (projectionValue 1 xs)
  have h32 := binaryRecover liveState (q26 mw) (.projection 5) (ys 32) (ys 26) framedResults xs (hq 32) (hq 26) (projectionValue 5 xs)
  have h33 := unaryRecover InternalListCodec.headCode (.projection 1) (ys 33) results xs (hq 33) (projectionValue 1 xs)
  have h34 := unaryRecover InternalListCodec.tailCode (.projection 1) (ys 34) results xs (hq 34) (projectionValue 1 xs)
  have h35 := unaryRecover InternalListCodec.headCode (q34) (ys 35) (ys 34) xs (hq 35) (hq 34)
  have h36 := unaryRecover InternalListCodec.tailCode (q34) (ys 36) (ys 34) xs (hq 36) (hq 34)
  have h37 : Nonempty (Derivation body Gamma (programGraph combine (ys 37) (Fin.cons (ys 5) (Fin.cons (ys 4) (Fin.cons (ys 35) (Fin.cons (ys 33) (Fin.cons parameter Fin.elim0))))))) := by
    apply compositionRecover combine ![(q5),(q4),(q35),(q33),(.projection 6)] (ys 37) xs
      (Fin.cons (ys 5) (Fin.cons (ys 4) (Fin.cons (ys 35) (Fin.cons (ys 33) (Fin.cons parameter Fin.elim0))))) (hq 37)
    intro k
    exact Fin.cases (hq 5) (Fin.cases (hq 4) (Fin.cases (hq 35)
      (Fin.cases (hq 33) (Fin.cases (projectionValue 6 xs) (fun t => Fin.elim0 t))))) k
  have h38 := binaryRecover (extend mr) (q36) (.projection 3) (ys 38) (ys 36) resultBackground xs (hq 38) (hq 36) (projectionValue 3 xs)
  have h39 := binaryRecover (extend mr) (q34) (.projection 3) (ys 39) (ys 34) resultBackground xs (hq 39) (hq 34) (projectionValue 3 xs)
  have h40 := binaryRecover InternalListCodec.consCode (q37 combine) (q36) (ys 40) (ys 37) (ys 36) xs (hq 40) (hq 37) (hq 36)
  have h41 := binaryRecover InternalListCodec.consCode (q37 combine) (q38 mr) (ys 41) (ys 37) (ys 38) xs (hq 41) (hq 37) (hq 38)
  have h42 := binaryRecover liveState (q1) (q40 combine) (ys 42) (ys 1) (ys 40) xs (hq 42) (hq 1) (hq 40)
  have h43 := binaryRecover liveState (q13 mw) (q41 mr combine) (ys 43) (ys 13) (ys 41) xs (hq 43) (hq 13) (hq 41)

  have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero stack (ys 0) (ys 1) hn h0 h1
  have hfc := extendConsForward mw stack (ys 0) (ys 1) workBackground (ys 13) framedStack hc h13 hw
  have hp := reconstructPair (ys 0) (ys 2) (ys 3) h2 h3
  have hpv := reconstructPair (ys 3) (ys 5) (ys 4) h5 h4
  have hpn := reconstructPair (ys 4) (ys 6) (ys 7) h6 h7
  have hpb := reconstructPair (ys 7) (ys 8) (ys 9) h8 h9
  have hpch := reconstructPair (ys 9) (ys 10) (ys 11) h10 h11
  have hLeafFrame := extendConsBackward mr (ys 27) (ys 12) results resultBackground framedResults (ys 28) h27 hr h28
  have hFinFrame := extendConsBackward mw (ys 21) (ys 20) (ys 1) workBackground (ys 13) (ys 24) h21 h13 h24
  have hArgFrame := extendConsBackward mw (ys 22) (ys 18) (ys 21) workBackground (ys 24) (ys 25) h22 hFinFrame h25
  have hExpFrame := extendConsBackward mw (ys 23) (ys 17) (ys 22) workBackground (ys 25) (ys 26) h23 hArgFrame h26
  have hCombFrame := extendConsBackward mr (ys 40) (ys 37) (ys 36) resultBackground (ys 38) (ys 41) h40 h38 h41
  let vp : Fin 1 → OTerm α := Fin.cons (ys 3) Fin.elim0
  have rootTagGraph : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationStepPeel.constructorTag (.projection 0)) (ys 6) (ys 3))) :=
    unaryValue InternalUnpair.left (rightOf (.projection 0)) (ys 6) (ys 4) vp h6
      (unaryValue InternalUnpair.right (.projection 0) (ys 4) (ys 3) vp h4 (projectionValue 0 vp))
  have leafCase : ∀ (Delta : List (Formula α)) (inc : ∀ p ∈ Gamma, p ∈ Delta),
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) z (ys 3))) →
      Nonempty (Derivation body Delta (graph2 (openGuardP guard) z (ys 3) parameter)) →
      Nonempty (Derivation body Delta psi) := by
    intro Delta inc hvisit hopen
    apply klive Delta (ys 1) (ys 13) (ys 27) (ys 28) (ys 29) (ys 30) inc
      (weakenProof h13 inc) (weakenProof hLeafFrame inc) (weakenProof h29 inc) (weakenProof h30 inc)
    · exact leafTransitionAt guard leaf combine parameter state stack results (ys 0) (ys 3) (ys 1)
        (ys 29) (ys 12) (ys 27) (weakenProof hs inc) (weakenProof hc inc) hvisit hopen
        (weakenProof h12 inc) (weakenProof h27 inc) (weakenProof h29 inc)
    · exact leafTransitionAt guard leaf combine parameter framedState framedStack framedResults (ys 0) (ys 3) (ys 13)
        (ys 30) (ys 12) (ys 28) (weakenProof hfs inc) (weakenProof hfc inc) hvisit hopen
        (weakenProof h12 inc) (weakenProof h28 inc) (weakenProof h30 inc)
  have expandCase : ∀ (Delta : List (Formula α)) (inc : ∀ p ∈ Gamma, p ∈ Delta),
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) z (ys 3))) →
      Nonempty (Derivation body Delta (graph4 packedApplication (ys 3) (ys 8) (ys 5) (ys 10) (ys 11))) →
      Nonempty (Derivation body Delta (graph2 guard (suc z) (ys 3) parameter)) →
      Nonempty (Derivation body Delta psi) := by
    intro Delta inc hvisit happ hguard
    apply klive Delta (ys 23) (ys 26) results framedResults (ys 31) (ys 32) inc
      (weakenProof hExpFrame inc) (weakenProof hr inc) (weakenProof h31 inc) (weakenProof h32 inc)
    · apply InternalParameterizedApplicationResultStackVisitProof.visitBackward guard leaf combine
        (ys 8) (ys 5) (ys 10) (ys 11) (ys 3) (ys 1) results state (ys 31) parameter happ
        (visitStateAt state stack results (ys 0) (ys 3) (ys 1) (weakenProof hs inc) (weakenProof hc inc) hvisit) hguard
      exact expandedStateAt (ys 31) (ys 23) results (ys 8) (ys 5) (ys 10) (ys 11) (ys 1)
        (ys 14) (ys 15) (ys 16) (ys 17) (ys 18) (ys 19) (ys 20) (ys 21) (ys 22)
        (weakenProof h31 inc) (weakenProof h14 inc) (weakenProof h15 inc) (weakenProof h16 inc)
        (weakenProof h17 inc) (weakenProof h18 inc) (weakenProof h19 inc) (weakenProof h20 inc)
        (weakenProof h21 inc) (weakenProof h22 inc) (weakenProof h23 inc)
    · apply InternalParameterizedApplicationResultStackVisitProof.visitBackward guard leaf combine
        (ys 8) (ys 5) (ys 10) (ys 11) (ys 3) (ys 13) framedResults framedState (ys 32) parameter happ
        (visitStateAt framedState framedStack framedResults (ys 0) (ys 3) (ys 13)
          (weakenProof hfs inc) (weakenProof hfc inc) hvisit) hguard
      exact expandedStateAt (ys 32) (ys 26) framedResults (ys 8) (ys 5) (ys 10) (ys 11) (ys 13)
        (ys 14) (ys 15) (ys 16) (ys 17) (ys 18) (ys 19) (ys 20) (ys 24) (ys 25)
        (weakenProof h32 inc) (weakenProof h14 inc) (weakenProof h15 inc) (weakenProof h16 inc)
        (weakenProof h17 inc) (weakenProof h18 inc) (weakenProof h19 inc) (weakenProof h20 inc)
        (weakenProof h24 inc) (weakenProof h25 inc) (weakenProof h26 inc)
  have finishCase : ∀ (Delta : List (Formula α)) (inc : ∀ p ∈ Gamma, p ∈ Delta),
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) (suc z) (ys 3))) →
      Nonempty (Derivation body Delta (eqn results z).not) →
      Nonempty (Derivation body Delta (eqn (ys 34) z).not) →
      Nonempty (Derivation body Delta psi) := by
    intro Delta inc hfinish hnres hntail
    have hres := InternalListCodecDecompositionSupportProof.reconstructNonzero results (ys 33) (ys 34)
      hnres (weakenProof h33 inc) (weakenProof h34 inc)
    have htail := InternalListCodecDecompositionSupportProof.reconstructNonzero (ys 34) (ys 35) (ys 36)
      hntail (weakenProof h35 inc) (weakenProof h36 inc)
    have hfres := extendConsForward mr results (ys 33) (ys 34) resultBackground (ys 39) framedResults
      hres (weakenProof h39 inc) (weakenProof hr inc)
    have hftail := extendConsForward mr (ys 34) (ys 35) (ys 36) resultBackground (ys 38) (ys 39)
      htail (weakenProof h38 inc) (weakenProof h39 inc)
    apply klive Delta (ys 1) (ys 13) (ys 40) (ys 41) (ys 42) (ys 43) inc
      (weakenProof h13 inc) (weakenProof hCombFrame inc) (weakenProof h42 inc) (weakenProof h43 inc)
    · exact finishTransitionAt guard leaf combine parameter state stack results (ys 0) (ys 3) (ys 5) (ys 4) (ys 1)
        (ys 33) (ys 35) (ys 36) (ys 34) (ys 42) (ys 37) (ys 40)
        (weakenProof hs inc) (weakenProof hc inc) hfinish (weakenProof hpv inc) hres htail
        (weakenProof h37 inc) (weakenProof h40 inc) (weakenProof h42 inc)
    · exact finishTransitionAt guard leaf combine parameter framedState framedStack framedResults (ys 0) (ys 3) (ys 5) (ys 4) (ys 13)
        (ys 33) (ys 35) (ys 38) (ys 39) (ys 43) (ys 37) (ys 41)
        (weakenProof hfs inc) (weakenProof hfc inc) hfinish (weakenProof hpv inc) hfres hftail
        (weakenProof h37 inc) (weakenProof h41 inc) (weakenProof h43 inc)
  apply equalityCases (ys 2) z psi
  · intro Delta inc htag0
    apply equalityCases (ys 2) (suc z) psi
    · intro Theta inc2 htag1
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      apply kfail Theta inc3
      exact malformedFailure guard leaf combine parameter state stack results (ys 0) (ys 1) (ys 2) (ys 3)
        (weakenProof hs inc3) (weakenProof hc inc3) (weakenProof hp inc3)
        (weakenProof htag0 inc2) htag1
    · intro Theta inc2 htag1
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have hfinish := headTransport InternalPairing.pairing (ys 0) (ys 2) (suc z)
        (Fin.cons (ys 3) Fin.elim0) (InternalEqualityTestProof.equalityOfAcceptance (ys 2) (suc z) htag1)
        (weakenProof hp inc3)
      apply formulaCases (eqn results z)
      · have inc4 : ∀ p ∈ Gamma, p ∈ (eqn results z :: Theta) := fun p hp => List.mem_cons_of_mem _ (inc3 p hp)
        apply kfail _ inc4
        exact emptyResultsFailure guard leaf combine parameter state stack (ys 0) (ys 1) (ys 2) (ys 3)
          (rightTransport liveState state stack results z ⟨Derivation.hypothesis List.mem_cons_self⟩
            (weakenProof hs inc4)) (weakenProof hc inc4) (weakenProof hp inc4)
          (weakenProof htag0 (fun p hp => List.mem_cons_of_mem _ (inc2 p hp)))
          (weakenProof htag1 (fun p hp => List.mem_cons_of_mem _ hp))
      · let Xi := (eqn results z).not :: Theta
        have inc4 : ∀ p ∈ Gamma, p ∈ Xi := fun p hp => List.mem_cons_of_mem _ (inc3 p hp)
        have hnres : Nonempty (Derivation body Xi (eqn results z).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply formulaCases (eqn (ys 34) z)
        · have inc5 : ∀ p ∈ Gamma, p ∈ (eqn (ys 34) z :: Xi) := fun p hp => List.mem_cons_of_mem _ (inc4 p hp)
          have hres := InternalListCodecDecompositionSupportProof.reconstructNonzero results (ys 33) (ys 34)
            (weakenProof hnres (fun p hp => List.mem_cons_of_mem _ hp))
            (weakenProof h33 inc5) (weakenProof h34 inc5)
          have hres0 := rightTransport InternalListCodec.consCode results (ys 33) (ys 34) z
            ⟨Derivation.hypothesis List.mem_cons_self⟩ hres
          apply kfail _ inc5
          exact singletonResultsFailure guard leaf combine parameter state stack results (ys 0) (ys 1) (ys 2) (ys 3) (ys 33)
            (weakenProof hs inc5) (weakenProof hc inc5) (weakenProof hp inc5) hres0
            (weakenProof htag0 (fun p hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (inc2 p hp))))
            (weakenProof htag1 (fun p hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
        · have inc5 : ∀ p ∈ Gamma, p ∈ ((eqn (ys 34) z).not :: Xi) := fun p hp => List.mem_cons_of_mem _ (inc4 p hp)
          exact finishCase _ inc5
            (weakenProof hfinish (fun p hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
            (weakenProof hnres (fun p hp => List.mem_cons_of_mem _ hp)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro Delta inc htag0
    have hvisit := headTransport InternalPairing.pairing (ys 0) (ys 2) z
      (Fin.cons (ys 3) Fin.elim0) (InternalEqualityTestProof.equalityOfAcceptance (ys 2) z htag0)
      (weakenProof hp inc)
    apply equalityCases (ys 6) positionTerm psi
    · intro Theta inc2 hroot
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have htest := binaryValue InternalEqualityTest.equalityTest
        (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1) z (ys 6) positionTerm vp
        hroot (weakenProof rootTagGraph inc3) (twoValue vp)
      exact leafCase Theta inc3 (weakenProof hvisit inc2) (conjunctionRejectLeft _ guard (Fin.cons (ys 3) (Fin.cons parameter Fin.elim0))
        (liftValue _ z (ys 3) parameter htest))
    · intro Theta inc2 hroot
      have inc3 : ∀ p ∈ Gamma, p ∈ Theta := fun p hp => inc2 p (inc p hp)
      have htest := binaryValue InternalEqualityTest.equalityTest
        (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1) (suc z) (ys 6) positionTerm vp
        hroot (weakenProof rootTagGraph inc3) (twoValue vp)
      have hnode := headTransport InternalPairing.pairing (ys 4) (ys 6) positionTerm
        (Fin.cons (ys 7) Fin.elim0) (InternalEqualityTestProof.equalityOfAcceptance (ys 6) positionTerm hroot)
        (weakenProof hpn inc3)
      have happ := packedAtPairs (ys 8) (ys 5) (ys 10) (ys 11) (ys 9) (ys 7) (ys 4) (ys 3)
        (weakenProof hpch inc3) (weakenProof hpb inc3) hnode (weakenProof hpv inc3)
      apply formulaCases (graph2 guard (suc z) (ys 3) parameter)
      · have inc4 : ∀ p ∈ Gamma, p ∈ (graph2 guard (suc z) (ys 3) parameter :: Theta) := fun p hp => List.mem_cons_of_mem _ (inc3 p hp)
        exact expandCase _ inc4
          (weakenProof hvisit (fun p hp => List.mem_cons_of_mem _ (inc2 p hp)))
          (weakenProof happ (fun p hp => List.mem_cons_of_mem _ hp)) ⟨Derivation.hypothesis List.mem_cons_self⟩
      · have inc4 : ∀ p ∈ Gamma, p ∈ ((graph2 guard (suc z) (ys 3) parameter).not :: Theta) := fun p hp => List.mem_cons_of_mem _ (inc3 p hp)
        exact leafCase _ inc4 (weakenProof hvisit (fun p hp => List.mem_cons_of_mem _ (inc2 p hp)))
          (conjunctionRejectRight _ guard (Fin.cons (ys 3) (Fin.cons parameter Fin.elim0))
            (liftValue _ (suc z) (ys 3) parameter (weakenProof htest (fun p hp => List.mem_cons_of_mem _ hp)))
            ⟨Derivation.hypothesis List.mem_cons_self⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameCoreProof
