module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationResultStackComposition InternalApplicationResultStackCompositionSyntaxProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionRunProof
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem fuelAtPayload (value payload : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.fuel (payloadFuel payload) value)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  exact unaryValue .succ
    (.composition InternalArithmeticPrograms.addition ![InternalUnpair.right,InternalUnpair.right])
    (payloadFuel payload) (OrdinaryArithmetic.addTerm payload payload) xs
    (successorValue (Fin.cons (OrdinaryArithmetic.addTerm payload payload) Fin.elim0))
    (binaryValue InternalArithmeticPrograms.addition InternalUnpair.right InternalUnpair.right
      (OrdinaryArithmetic.addTerm payload payload) payload payload xs (InternalArithmeticProgramsSupportProof.additionValue payload payload) hp hp)

theorem initialIntro (value work state : OTerm α)
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work z))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.initial state value)) :=
  liveOfValue visitWork (InternalAcceptance.constantZero 1) state work z
    (Fin.cons value Fin.elim0) hs hw (constantZeroValue _)

theorem initialRecover (value work state : OTerm α)
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.initial state value))) :
    Nonempty (Derivation body Gamma (graph2 liveState state work z)) := by
  apply programCases liveState (Fin.cons work (Fin.cons z Fin.elim0)) _
  intro β j Delta actual hj ha
  simp only [graph2Rename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at ha
  have hw' := renameInto hw j Delta hj
  have hs' := renameInto hs j Delta hj
  simp only [graph1Rename] at hw' hs'
  have hi := initialIntro (value.relabel j) (work.relabel j) actual hw' ha
  have he := valueUnique InternalApplicationResultStack.initial actual (state.relabel j)
    (Fin.cons (value.relabel j) Fin.elim0) hi hs'
  exact outputTransport liveState actual (state.relabel j)
    (Fin.cons (work.relabel j) (Fin.cons z Fin.elim0)) he ha

theorem runOfCertifiedFold (guard leaf : Program 1) (combine : Program 4)
    (value payload work out singleton : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z)))
    (hf : Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out value))) :
    Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (payloadFuel payload) work z singleton)) := by
  apply queryCases ![InternalApplicationResultStack.initial,InternalApplicationResultStack.run guard leaf combine]
    (Fin.cons value Fin.elim0) _
  intro β j ys Delta hj hq
  simp only [actualRunRename,payloadFuelRename,zRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hp' := renameInto hp j Delta hj
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [graph1Rename] at hp' hw'
  simp only [graph2Rename,zRelabel] at hc'
  rw [certifiedFoldRename] at hf'
  let xs : Fin 1 → OTerm β := Fin.cons (value.relabel j) Fin.elim0
  have hg := unaryRecover goodState (InternalApplicationResultStack.run guard leaf combine)
    (suc z) (ys 1) xs (andLeft hf') (hq 1)
  have ho := unaryRecover InternalApplicationResultStack.output (InternalApplicationResultStack.run guard leaf combine)
    (out.relabel j) (ys 1) xs (andRight hf') (hq 1)
  exact runIntro guard leaf combine (payloadFuel (payload.relabel j)) (work.relabel j) z
    (singleton.relabel j) (ys 0) (ys 1)
    (initialRecover (value.relabel j) (work.relabel j) (ys 0) hw' (hq 0))
    (stateRecover (ys 1) (out.relabel j) (singleton.relabel j) hg ho hc')
    (binaryRecover (InternalApplicationResultStack.iterate guard leaf combine)
      InternalApplicationResultStack.fuel InternalApplicationResultStack.initial
      (ys 1) (payloadFuel (payload.relabel j)) (ys 0) xs (hq 1)
      (fuelAtPayload (value.relabel j) (payload.relabel j) hp') (hq 0))

theorem certifiedFoldOfRun (guard leaf : Program 1) (combine : Program 4)
    (value payload work out singleton : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload value)))
    (hw : Nonempty (Derivation body Gamma (graph1 visitWork work value)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z)))
    (hr : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (payloadFuel payload) work z singleton))) :
    Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out value)) := by
  apply runCases guard leaf combine (payloadFuel payload) work z singleton _ hr
  intro β j Delta state finalState hj hi he ht
  rw [certifiedFoldRename]
  simp only [zRelabel] at hi
  simp only [payloadFuelRename] at ht
  have hp' := renameInto hp j Delta hj
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  simp only [graph1Rename] at hp' hw'
  simp only [graph2Rename,zRelabel] at hc'
  let xs : Fin 1 → OTerm β := Fin.cons (value.relabel j) Fin.elim0
  have hr' : Nonempty (Derivation body Delta
      (graph1 (InternalApplicationResultStack.run guard leaf combine) finalState (value.relabel j))) :=
    binaryValue (InternalApplicationResultStack.iterate guard leaf combine)
      InternalApplicationResultStack.fuel InternalApplicationResultStack.initial
      finalState (payloadFuel (payload.relabel j)) state xs ht
      (fuelAtPayload (value.relabel j) (payload.relabel j) hp')
      (initialIntro (value.relabel j) (work.relabel j) state hw' hi)
  have hf := stateIntro finalState (out.relabel j) (singleton.relabel j) he hc'
  exact andIntro
    (unaryValue goodState (InternalApplicationResultStack.run guard leaf combine) (suc z) finalState xs
      (andLeft hf) hr')
    (unaryValue InternalApplicationResultStack.output (InternalApplicationResultStack.run guard leaf combine)
      (out.relabel j) finalState xs (andRight hf) hr')

theorem actualOriginalCertifiedResultFoldRunBridge :
    InternalApplicationCertifiedResultFoldClosureTargets.ActualOriginalCertifiedResultFoldRunBridge := by
  intro body guard leaf combine α value payload work out singleton
  let c := graph1 InternalUnpair.right payload value ⊓
    (graph1 visitWork work value ⊓ graph2 InternalListCodec.consCode singleton out z)
  let f := certifiedFold guard leaf combine out value
  let r := actualRun guard leaf combine (payloadFuel payload) work z singleton
  have hc₁ : Nonempty (Derivation body [f,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := runOfCertifiedFold guard leaf combine value payload work out singleton
    (andLeft hc₁) (andLeft (andRight hc₁)) (andRight (andRight hc₁))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := certifiedFoldOfRun guard leaf combine value payload work out singleton
    (andLeft hc₂) (andLeft (andRight hc₂)) (andRight (andRight hc₂))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
