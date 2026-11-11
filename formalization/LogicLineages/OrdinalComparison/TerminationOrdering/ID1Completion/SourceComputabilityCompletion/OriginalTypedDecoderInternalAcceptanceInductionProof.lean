module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof OriginalTypedDecoderInternalAcceptanceRunProof
open OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof OriginalTypedDecoderInternalAcceptanceInductionCoreProof
open OriginalTypedDecoderInternalAcceptanceCouplingFrameProof
open InternalNumericIterationProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonemptyAtStates (H : Program 1)
    (count second frontWork suffix joined initial joinedInitial : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial (suc z) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing joinedInitial (suc z) joined))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (add (suc count) second) joined)) := by
  have hr := successfulWorkAt H (suc count) frontWork initial hp hf
  apply frameCases H frontWork suffix joined initial joinedInitial _ hn ha hp hjp
  · intro β j Delta hj ht _
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel,sucRelabel] at hr'
    have hbad := iterateAfterFirstRecover H
      (count.relabel j) (initial.relabel j) z (numeral 2) ht hr'
    obtain ⟨hbot⟩ := failureImpossible H (count.relabel j) hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta frontNext joinedNext nextState joinedNextState hj haNext hpNext hjpNext ht hjt
    simp only [OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,addRelabel,sucRelabel]
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel,sucRelabel] at hr'
    have hrow' := renameInto hrow j Delta hj
    rw [appendRowRename] at hrow'
    have hs' := renameInto hs j Delta hj
    rw [OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkRename] at hs'
    have hjp' := renameInto hjp j Delta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hjp'
    have hnext := iterateAfterFirstRecover H
      (count.relabel j) (initial.relabel j) nextState (numeral 2) ht hr'
    have hdone := successfulWorkIntro H (count.relabel j) frontNext nextState hpNext hnext
    have hcombined := rowApply H (count.relabel j) (second.relabel j)
      frontNext (suffix.relabel j) joinedNext hrow' haNext hdone hs'
    have hcombinedRun := successfulWorkAt H (add (count.relabel j) (second.relabel j))
      joinedNext joinedNextState hjpNext hcombined
    have hrun := iterateAfterFirst H
      (add (count.relabel j) (second.relabel j))
      (joinedInitial.relabel j) joinedNextState (numeral 2) hjt hcombinedRun
    have hfinish := successfulWorkIntro H (suc (add (count.relabel j) (second.relabel j)))
      (joined.relabel j) (joinedInitial.relabel j) hjp' hrun
    exact countTransport H (suc (add (count.relabel j) (second.relabel j)))
      (add (suc (count.relabel j)) (second.relabel j)) (joined.relabel j)
      ⟨symm (leftSuccessor (count.relabel j) (second.relabel j))⟩ hfinish

def stateQueries : Fin 2 → Program 2 :=
  fun i => pairOf (InternalLessThan.constantOne 2) (.projection i)

theorem nonemptyCore (H : Program 1)
    (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (add (suc count) second) joined)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases stateQueries (Fin.cons frontWork (Fin.cons joined Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  rw [appendRowRename] at hrow'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hf' := renameInto hf j Delta hj
  simp only [OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,sucRelabel] at hf'
  have hs' := renameInto hs j Delta hj
  rw [OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkRename] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  have hp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
    (ys 0) (suc z) (frontWork.relabel j) xs (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)
  have hjp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (suc z) (joined.relabel j) xs (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 1 xs)
  exact nonemptyAtStates H (count.relabel j) (second.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1)
    hrow' ha' hf' hs' hn' hp hjp

theorem succCore (H : Program 1) (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H (suc count) frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (add (suc count) second) joined)) := by
  apply formulaCases (eqn frontWork z)
  · exact emptyCore H (suc count) second frontWork suffix joined
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · exact nonemptyCore H count second frontWork suffix joined
      (withHyp hrow _) (withHyp ha _) (withHyp hf _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (H : Program 1) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H count))) :
    Nonempty (Derivation body Gamma (appendRow H (suc count))) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := graph2 append joined frontWork suffix ⊓
    (SuccessfulWork H (suc n) frontWork ⊓ SuccessfulWork H second suffix)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [appendRowRename] at hrow'
  obtain ⟨d⟩ := succCore H n second frontWork suffix joined hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (H : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (appendRow H count)) := by
  let theta : Formula (α ⊕ Fin 1) := appendRow H (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,appendInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) H)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      H (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,appendSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,appendInstantiate,varBind] using (Nonempty.intro h)

theorem successfulAppend (H : Program 1)
    (first second frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H first frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (add first second) joined)) :=
  rowApply H first second frontWork suffix joined (allRows H first) ha hf hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionProof
