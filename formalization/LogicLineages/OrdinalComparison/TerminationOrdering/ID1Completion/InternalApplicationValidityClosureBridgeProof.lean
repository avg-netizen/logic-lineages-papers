module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationValidityStackAppend InternalApplicationValidityStackAppendSyntaxProof
open InternalApplicationValidityStackAppendTransitionProof InternalApplicationValidityStackAppendRunProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Recover a literal selector output from its original equality-test graph.
The intermediate value is supplied by internal Program totality. -/
theorem sameRecoverLeft {n : Nat} (p q : Program n) (value : OTerm α)
    (xs : Fin n → OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q value xs))) :
    Nonempty (Derivation body Gamma (programGraph p value xs)) := by
  apply programCases p xs _
  intro β j Delta actual hj hp
  simp only [programRename]
  have hs' := renameInto hs j Delta hj
  have hq' := renameInto hq j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at hs' hq'
  have he := binaryRecover InternalEqualityTest.equalityTest p q (suc z)
    actual (value.relabel j) (fun i => (xs i).relabel j) hs' hp hq'
  exact outputTransport p actual (value.relabel j) (fun i => (xs i).relabel j)
    (InternalEqualityTestProof.equalityOfAcceptance actual (value.relabel j) he) hp

/-- Finished acceptance supplies status one and an empty worklist, so the
original unpair reverse inverse reconstructs the arithmetic state TWO. -/
theorem finishedRecover (state : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 finished (suc z) state))) :
    Nonempty (Derivation body Gamma (eqn state successState)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hc := conjunctionRecover (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1)) xs h
  have hs := sameRecoverLeft status (InternalLessThan.constantOne 1) (suc z) xs
    (andLeft hc) (InternalLessThanSupportProof.oneConstantValue xs)
  have hw := sameRecoverLeft work (InternalAcceptance.constantZero 1) z xs
    (andRight hc) (constantZeroValue xs)
  exact valueUnique InternalPairing.pairing state successState
    (Fin.cons (suc z) (Fin.cons z Fin.elim0))
    (reconstructPair state (suc z) z hs hw) pairOneZero

/-- The literal terminal pair graph proves acceptance of the original
finished AST, with Boolean output one and arithmetic input two. -/
theorem finishedAtSuccess :
    Nonempty (Derivation body Gamma (graph1 finished (suc z) (successState : OTerm α))) := by
  let xs : Fin 1 → OTerm α := Fin.cons successState Fin.elim0
  apply conjunctionAccept (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1)) xs
  · exact sameAccept status (InternalLessThan.constantOne 1) (suc z) xs
      (pairLeft successState (suc z) z pairOneZero)
      (InternalLessThanSupportProof.oneConstantValue xs)
  · exact sameAccept work (InternalAcceptance.constantZero 1) z xs
      (pairRight successState (suc z) z pairOneZero) (constantZeroValue xs)

theorem finishedIntro (state : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn state successState))) :
    Nonempty (Derivation body Gamma (graph1 finished (suc z) state)) := by
  obtain ⟨h⟩ := h
  exact headTransport finished (suc z) successState state Fin.elim0 ⟨symm h⟩ finishedAtSuccess

theorem actualOriginalFinishedAcceptance :
    InternalApplicationValidityClosureTargets.ActualOriginalFinishedAcceptance := by
  intro body α state
  simp only [equalEqn]
  let p := graph1 finished (suc z) state
  let q := eqn state successState
  obtain ⟨hf⟩ := finishedRecover (body := body) (Gamma := [p]) state
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := finishedIntro (body := body) (Gamma := [q]) state
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The bound is exactly the successor of the actual original payload. -/
theorem fuelAtPayload (value payload : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value))) :
    Nonempty (Derivation body Gamma (graph1 fuel (suc payload) value)) :=
  unaryValue .succ InternalUnpair.right (suc payload) payload (Fin.cons value Fin.elim0)
    (successorValue (Fin.cons payload Fin.elim0)) hp

/-- The singleton is constrained by the actual successor/pair list constructor. -/
theorem singletonAt (value singleton : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode singleton value z))) :
    Nonempty (Derivation body Gamma
      (graph1 (consOf (.projection 0) (InternalAcceptance.constantZero 1)) singleton value)) :=
  binaryValue InternalListCodec.consCode (.projection 0) (InternalAcceptance.constantZero 1)
    singleton value z (Fin.cons value Fin.elim0) hs
    (projectionValue 0 (Fin.cons value Fin.elim0)) (constantZeroValue _)

theorem initialAtSingleton (value singleton state : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode singleton value z)))
    (hi : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing state (suc z) singleton))) :
    Nonempty (Derivation body Gamma (graph1 initial state value)) :=
  binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1)
    (consOf (.projection 0) (InternalAcceptance.constantZero 1))
    state (suc z) singleton (Fin.cons value Fin.elim0) hi
    (InternalLessThanSupportProof.oneConstantValue _) (singletonAt value singleton hs)

theorem initialSingletonRecover (value singleton state : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode singleton value z)))
    (hi : Nonempty (Derivation body Gamma (graph1 initial state value))) :
    Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing state (suc z) singleton)) :=
  binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1)
    (consOf (.projection 0) (InternalAcceptance.constantZero 1))
    state (suc z) singleton (Fin.cons value Fin.elim0) hi
    (InternalLessThanSupportProof.oneConstantValue _) (singletonAt value singleton hs)

/-- Eliminate the actual initial and run outputs, then use finished acceptance
and graph functionality. Neither the run count nor its initial state is free. -/
theorem singletonSuccessOfAcceptance (node leaf : Program 1)
    (value payload singleton : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode singleton value z)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) value))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf (suc payload) singleton)) := by
  apply queryCases ![initial,run node leaf] (Fin.cons value Fin.elim0) _
  intro β j ys Delta hj hq
  simp only [successfulWorkRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hp' := renameInto hp j Delta hj
  have hs' := renameInto hs j Delta hj
  have hv' := renameInto hv j Delta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hp' hs' hv'
  have hi : Nonempty (Derivation body Delta (graph1 initial (ys 0) (value.relabel j))) := hq 0
  have hr : Nonempty (Derivation body Delta
      (graph1 (run node leaf) (ys 1) (value.relabel j))) := hq 1
  have hf := unaryRecover finished (run node leaf) (suc z) (ys 1)
    (Fin.cons (value.relabel j) Fin.elim0) hv' hr
  have hi' := initialSingletonRecover (value.relabel j) (singleton.relabel j) (ys 0) hs' hi
  have hr' := binaryRecover (iterate node leaf) fuel initial (ys 1)
    (suc (payload.relabel j)) (ys 0) (Fin.cons (value.relabel j) Fin.elim0) hr
    (fuelAtPayload (value.relabel j) (payload.relabel j) hp') hi
  exact successfulWorkIntro node leaf (suc (payload.relabel j)) (singleton.relabel j) (ys 0)
    hi' (outputTransport (iterate node leaf) (ys 1) successState
      (Fin.cons (suc (payload.relabel j)) (Fin.cons (ys 0) Fin.elim0)) (finishedRecover (ys 1) hf) hr')

/-- Rebuild the frozen initial/fuel/run/finished composition at exactly the
singleton-success witness; no larger count or semantic reflection is used. -/
theorem acceptanceOfSingletonSuccess (node leaf : Program 1)
    (value payload singleton : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode singleton value z)))
    (hw : Nonempty (Derivation body Gamma (successfulWork node leaf (suc payload) singleton))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) value)) := by
  apply successfulWorkCases node leaf (suc payload) singleton _ hw
  intro β j Delta state hj hi hr
  simp only [graph1Rename,sucRelabel,zRelabel]
  simp only [sucRelabel] at hr
  have hp' := renameInto hp j Delta hj
  have hs' := renameInto hs j Delta hj
  simp only [graph1Rename,graph2Rename,zRelabel] at hp' hs'
  have hi' := initialAtSingleton (value.relabel j) (singleton.relabel j) state hs' hi
  have hr' : Nonempty (Derivation body Delta
      (graph1 (run node leaf) successState (value.relabel j))) :=
    binaryValue (iterate node leaf) fuel initial successState (suc (payload.relabel j)) state
      (Fin.cons (value.relabel j) Fin.elim0) hr
      (fuelAtPayload (value.relabel j) (payload.relabel j) hp') hi'
  exact unaryValue finished (run node leaf) (suc z) successState
    (Fin.cons (value.relabel j) Fin.elim0) finishedAtSuccess hr'

theorem actualOriginalValidatorSingletonSuccess :
    InternalApplicationValidityClosureTargets.ActualOriginalValidatorSingletonSuccess := by
  intro body node leaf α value payload singleton
  let c := graph1 InternalUnpair.right payload value ⊓
    graph2 InternalListCodec.consCode singleton value z
  let g := graph1 (validator node leaf) (suc z) value
  let r := successfulWork node leaf (suc payload) singleton
  have hc₁ : Nonempty (Derivation body [g,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := singletonSuccessOfAcceptance node leaf value payload singleton
    (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := acceptanceOfSingletonSuccess node leaf value payload singleton
    (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureBridgeProof
