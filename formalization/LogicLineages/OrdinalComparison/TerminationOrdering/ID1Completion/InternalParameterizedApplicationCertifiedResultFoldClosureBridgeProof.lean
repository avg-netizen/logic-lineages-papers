module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open InternalParameterizedApplicationResultStack
open InternalParameterizedApplicationResultStackCompositionSyntaxProof
open InternalParameterizedApplicationResultStackCompositionRunProof
open InternalParameterizedApplicationResultStackWiringProof
open InternalApplicationCertifiedResultFoldClosureBridgeProof (fuelAtPayload initialIntro initialRecover)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The actual runP composition at its original fuel and original initial state. -/
theorem runValueAt (guard leaf : Program 2) (combine : Program 5)
    (value payload parameter state finalState : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.initial state value)))
    (ht : Nonempty (Derivation body Gamma
      (graph3 (iterateP guard leaf combine) finalState (payloadFuel payload) state parameter))) :
    Nonempty (Derivation body Gamma (graph2 (runP guard leaf combine) finalState value parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons parameter Fin.elim0)
  apply compositionValue (iterateP guard leaf combine)
    ![liftP InternalApplicationResultStack.fuel,liftP InternalApplicationResultStack.initial,.projection 1]
    finalState xs (Fin.cons (payloadFuel payload) (Fin.cons state (Fin.cons parameter Fin.elim0))) ht
  intro i
  exact Fin.cases (liftValue InternalApplicationResultStack.fuel (payloadFuel payload) value parameter
    (fuelAtPayload value payload hp))
    (Fin.cases (liftValue InternalApplicationResultStack.initial state value parameter hi)
      (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem runRecoverAt (guard leaf : Program 2) (combine : Program 5)
    (value payload parameter state finalState : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.initial state value)))
    (hr : Nonempty (Derivation body Gamma (graph2 (runP guard leaf combine) finalState value parameter))) :
    Nonempty (Derivation body Gamma
      (graph3 (iterateP guard leaf combine) finalState (payloadFuel payload) state parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons parameter Fin.elim0)
  apply compositionRecover (iterateP guard leaf combine)
    ![liftP InternalApplicationResultStack.fuel,liftP InternalApplicationResultStack.initial,.projection 1]
    finalState xs (Fin.cons (payloadFuel payload) (Fin.cons state (Fin.cons parameter Fin.elim0))) hr
  intro i
  exact Fin.cases (liftValue InternalApplicationResultStack.fuel (payloadFuel payload) value parameter
    (fuelAtPayload value payload hp))
    (Fin.cases (liftValue InternalApplicationResultStack.initial state value parameter hi)
      (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem runOfCertifiedFold (guard leaf : Program 2) (combine : Program 5)
    (value payload work out singleton parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z)))
    (hf : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out value parameter))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (payloadFuel payload) work z singleton)) := by
  apply queryCases ![liftP InternalApplicationResultStack.initial,runP guard leaf combine]
    (Fin.cons value (Fin.cons parameter Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [actualRunRename,payloadFuelRename,zRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hp' := renameInto hp j Delta hj
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [graph1Rename] at hp' hw'
  simp only [graph2Rename,zRelabel] at hc'
  rw [certifiedFoldPRename] at hf'
  let xs : Fin 2 → OTerm β := Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hi := liftRecover InternalApplicationResultStack.initial (ys 0) (value.relabel j)
    (parameter.relabel j) (hq 0)
  have hg := unaryRecover goodState (runP guard leaf combine)
    (suc z) (ys 1) xs (andLeft hf') (hq 1)
  have ho := unaryRecover InternalApplicationResultStack.output (runP guard leaf combine)
    (out.relabel j) (ys 1) xs (andRight hf') (hq 1)
  exact runIntro guard leaf combine (parameter.relabel j) (payloadFuel (payload.relabel j))
    (work.relabel j) z (singleton.relabel j) (ys 0) (ys 1)
    (initialRecover (value.relabel j) (work.relabel j) (ys 0) hw' hi)
    (stateRecover (ys 1) (out.relabel j) (singleton.relabel j) hg ho hc')
    (runRecoverAt guard leaf combine (value.relabel j) (payload.relabel j) (parameter.relabel j)
      (ys 0) (ys 1) hp' hi (hq 1))

theorem certifiedFoldOfRun (guard leaf : Program 2) (combine : Program 5)
    (value payload work out singleton parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (payloadFuel payload) work z singleton))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out value parameter)) := by
  apply runCases guard leaf combine parameter (payloadFuel payload) work z singleton _ hr
  intro β j Delta state finalState hj hi he ht
  rw [certifiedFoldPRename]
  simp only [zRelabel] at hi
  simp only [payloadFuelRename] at ht
  have hp' := renameInto hp j Delta hj
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  simp only [graph1Rename] at hp' hw'
  simp only [graph2Rename,zRelabel] at hc'
  let xs : Fin 2 → OTerm β := Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hr' := runValueAt guard leaf combine (value.relabel j) (payload.relabel j)
    (parameter.relabel j) state finalState hp'
    (initialIntro (value.relabel j) (work.relabel j) state hw' hi) ht
  have hf := stateIntro finalState (out.relabel j) (singleton.relabel j) he hc'
  exact andIntro
    (unaryValue goodState (runP guard leaf combine) (suc z) finalState xs (andLeft hf) hr')
    (unaryValue InternalApplicationResultStack.output (runP guard leaf combine)
      (out.relabel j) finalState xs (andRight hf) hr')

theorem actualOriginalParameterizedCertifiedResultFoldRunBridge :
    InternalParameterizedApplicationCertifiedResultFoldClosureTargets.ActualOriginalParameterizedCertifiedResultFoldRunBridge := by
  intro body guard leaf combine α Gamma value payload work out singleton parameter
  let c := graph1 InternalUnpair.right payload value ⊓
    (graph1 visitWork work value ⊓ graph2 InternalListCodec.consCode singleton out z)
  let f := certifiedFoldP guard leaf combine out value parameter
  let r := run guard leaf combine parameter (payloadFuel payload) work z singleton
  have hc₁ : Nonempty (Derivation body (f :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := runOfCertifiedFold guard leaf combine value payload work out singleton parameter
    (andLeft hc₁) (andLeft (andRight hc₁)) (andRight (andRight hc₁))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := certifiedFoldOfRun guard leaf combine value payload work out singleton parameter
    (andLeft hc₂) (andLeft (andRight hc₂)) (andRight (andRight hc₂))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
