module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendRunProof
open InternalApplicationValidityStackAppendInductionSyntaxProof InternalApplicationValidityStackAppendInductionCoreProof
open InternalApplicationValidityStackAppendFrameProof
open InternalNumericIterationProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonemptyAtStates (node leaf : Program 1)
    (count second frontWork suffix joined initial joinedInitial : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow node leaf count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial (suc z) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing joinedInitial (suc z) joined))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf (add (suc count) second) joined)) := by
  have hr := successfulWorkAt node leaf (suc count) frontWork initial hp hf
  apply frameCases node leaf frontWork suffix joined initial joinedInitial _ hn ha hp hjp
  · intro β j Delta hj ht _
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,successStateRename,sucRelabel] at hr'
    have hbad := frontSuccForward (InternalApplicationValidityStack.transition node leaf)
      (count.relabel j) successState (initial.relabel j) z ht hr'
    obtain ⟨hbot⟩ := failureImpossible node leaf (count.relabel j) hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta frontNext joinedNext nextState joinedNextState hj haNext hpNext hjpNext ht hjt
    simp only [successfulWorkRename,addRelabel,sucRelabel]
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,successStateRename,sucRelabel] at hr'
    have hrow' := renameInto hrow j Delta hj
    rw [appendRowRename] at hrow'
    have hs' := renameInto hs j Delta hj
    rw [successfulWorkRename] at hs'
    have hjp' := renameInto hjp j Delta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hjp'
    have hnext := frontSuccForward (InternalApplicationValidityStack.transition node leaf)
      (count.relabel j) successState (initial.relabel j) nextState ht hr'
    have hdone := successfulWorkIntro node leaf (count.relabel j) frontNext nextState hpNext hnext
    have hcombined := rowApply node leaf (count.relabel j) (second.relabel j)
      frontNext (suffix.relabel j) joinedNext hrow' haNext hdone hs'
    have hcombinedRun := successfulWorkAt node leaf (add (count.relabel j) (second.relabel j))
      joinedNext joinedNextState hjpNext hcombined
    have hrun := frontSuccBackward (InternalApplicationValidityStack.transition node leaf)
      (add (count.relabel j) (second.relabel j)) successState
      (joinedInitial.relabel j) joinedNextState hjt hcombinedRun
    have hfinish := successfulWorkIntro node leaf (suc (add (count.relabel j) (second.relabel j)))
      (joined.relabel j) (joinedInitial.relabel j) hjp' hrun
    exact countTransport node leaf (suc (add (count.relabel j) (second.relabel j)))
      (add (suc (count.relabel j)) (second.relabel j)) (joined.relabel j)
      ⟨symm (leftSuccessor (count.relabel j) (second.relabel j))⟩ hfinish

def stateQueries : Fin 2 → Program 2 :=
  fun i => pairOf (InternalLessThan.constantOne 2) (.projection i)

theorem nonemptyCore (node leaf : Program 1)
    (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow node leaf count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma (successfulWork node leaf (add (suc count) second) joined)) := by
  apply queryCases stateQueries (Fin.cons frontWork (Fin.cons joined Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [successfulWorkRename,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  rw [appendRowRename] at hrow'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hf' := renameInto hf j Delta hj
  simp only [successfulWorkRename,sucRelabel] at hf'
  have hs' := renameInto hs j Delta hj
  rw [successfulWorkRename] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  have hp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
    (ys 0) (suc z) (frontWork.relabel j) xs (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)
  have hjp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (suc z) (joined.relabel j) xs (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 1 xs)
  exact nonemptyAtStates node leaf (count.relabel j) (second.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1)
    hrow' ha' hf' hs' hn' hp hjp

theorem succCore (node leaf : Program 1) (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow node leaf count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf (add (suc count) second) joined)) := by
  apply formulaCases (eqn frontWork z)
  · exact emptyCore node leaf (suc count) second frontWork suffix joined
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · exact nonemptyCore node leaf count second frontWork suffix joined
      (withHyp hrow _) (withHyp ha _) (withHyp hf _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (node leaf : Program 1) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow node leaf count))) :
    Nonempty (Derivation body Gamma (appendRow node leaf (suc count))) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := graph2 append joined frontWork suffix ⊓
    (successfulWork node leaf (suc n) frontWork ⊓ successfulWork node leaf second suffix)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [appendRowRename] at hrow'
  obtain ⟨d⟩ := succCore node leaf n second frontWork suffix joined hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (node leaf : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (appendRow node leaf count)) := by
  let theta : Formula (α ⊕ Fin 1) := appendRow node leaf (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,appendInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) node leaf)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      node leaf (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,appendSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,appendInstantiate,varBind] using (Nonempty.intro h)

theorem actualOriginalSuccessfulWorkAppend :
    InternalApplicationValidityStackAppendTargets.ActualOriginalSuccessfulWorkAppend := by
  intro body node leaf α first second frontWork suffix joined
  let A := graph2 append joined frontWork suffix ⊓
    (successfulWork node leaf first frontWork ⊓ successfulWork node leaf second suffix)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := rowApply node leaf first second frontWork suffix joined (allRows node leaf first)
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionProof
