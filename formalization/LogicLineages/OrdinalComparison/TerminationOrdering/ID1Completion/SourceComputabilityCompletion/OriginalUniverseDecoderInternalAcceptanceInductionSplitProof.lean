module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof OriginalUniverseDecoderInternalAcceptanceRunProof
open OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof OriginalUniverseDecoderInternalAcceptanceInductionSplitCoreProof
open OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
open InternalNumericIterationProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonemptyAtStates (H : Program 1) (M W : Program 2)
    (count frontWork suffix joined initial joinedInitial c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) joined c)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hp : Nonempty (Derivation body Gamma (StepLive initial frontWork)))
    (hjp : Nonempty (Derivation body Gamma (StepLive joinedInitial joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (suc count) frontWork c ⊓ SuccessfulWork H M W (suc count) suffix c)) := by
  have hr := successfulWorkAt H M W (suc count) joined joinedInitial c hjp hs
  apply frameCases H M W frontWork suffix joined initial joinedInitial c _ hn ha hp hjp
  · intro β j Delta hj _ ht
    have hr' := renameInto hr j Delta hj
    simp only [graph3Rename,numeral,sucRelabel,zRelabel] at hr'
    have hbad := iterateAfterFirstRecover H M W
      (count.relabel j) (joinedInitial.relabel j) z (numeral 2) (c.relabel j) ht hr'
    obtain ⟨hbot⟩ := failureImpossible H M W (count.relabel j) (c.relabel j) hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta frontNext joinedNext nextState joinedNextState hj haNext hpNext hjpNext ht hjt
    simp only [conjunctionRename,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,sucRelabel]
    have hr' := renameInto hr j Delta hj
    simp only [graph3Rename,numeral,sucRelabel,zRelabel] at hr'
    have hrow' := renameInto hrow j Delta hj
    rw [splitRowRename] at hrow'
    have hp' := renameInto hp j Delta hj
    simp only [OriginalTypedDecoderInternalScalarSyntaxProof.stepLiveRename] at hp'
    have hnext := iterateAfterFirstRecover H M W
      (count.relabel j) (joinedInitial.relabel j) joinedNextState (numeral 2) (c.relabel j) hjt hr'
    have hdone := successfulWorkIntro H M W (count.relabel j) joinedNext joinedNextState (c.relabel j) hjpNext hnext
    have hsplit := splitRowApply H M W (count.relabel j)
      frontNext (suffix.relabel j) joinedNext (c.relabel j) hrow' haNext hdone
    have hfRun := successfulWorkAt H M W (count.relabel j)
      frontNext nextState (c.relabel j) hpNext (OriginalLambdaConstructorGraphSyntaxProof.andLeft hsplit)
    have hrun := iterateAfterFirst H M W
      (count.relabel j) (initial.relabel j) nextState (numeral 2) (c.relabel j) ht hfRun
    have hfront := successfulWorkIntro H M W (suc (count.relabel j))
      (frontWork.relabel j) (initial.relabel j) (c.relabel j) hp' hrun
    have hpad := successPadding H M W (count.relabel j) (suc z) (suffix.relabel j) (c.relabel j) (OriginalLambdaConstructorGraphSyntaxProof.andRight hsplit)
    have he : Derivation body Delta (eqn (add (count.relabel j) (suc z)) (suc (count.relabel j))) :=
      trans (addSucc (count.relabel j) z) (congSuc (addZero (count.relabel j)))
    exact OriginalLambdaConstructorGraphSyntaxProof.andIntro hfront (countTransport H M W (add (count.relabel j) (suc z))
      (suc (count.relabel j)) (suffix.relabel j) (c.relabel j) ⟨he⟩ hpad)

def stateQueries : Fin 2 → Program 2 :=
  fun i => pairOf (InternalLessThan.constantOne 2) (.projection i)

theorem nonemptyCore (H : Program 1) (M W : Program 2)
    (count frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) joined c)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (suc count) frontWork c ⊓ SuccessfulWork H M W (suc count) suffix c)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases stateQueries (Fin.cons frontWork (Fin.cons joined Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [conjunctionRename,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  rw [splitRowRename] at hrow'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Delta hj
  simp only [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,sucRelabel] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  have hp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
    (ys 0) (suc z) (frontWork.relabel j) xs (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)
  have hjp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (suc z) (joined.relabel j) xs (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 1 xs)
  exact nonemptyAtStates H M W (count.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1) (c.relabel j)
    hrow' ha' hs' hn' hp hjp

theorem succCore (H : Program 1) (M W : Program 2) (count frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) joined c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (suc count) frontWork c ⊓ SuccessfulWork H M W (suc count) suffix c)) := by
  apply formulaCases (eqn frontWork z)
  · exact splitEmptyCore H M W (suc count) frontWork suffix joined c
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · exact nonemptyCore H M W count frontWork suffix joined c
      (withHyp hrow _) (withHyp ha _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (H : Program 1) (M W : Program 2) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H M W count))) :
    Nonempty (Derivation body Gamma (splitRow H M W (suc count))) := by
  unfold splitRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let c : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := graph2 append joined frontWork suffix ⊓ SuccessfulWork H M W (suc n) joined c
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [splitRowRename] at hrow'
  obtain ⟨d⟩ := succCore H M W n frontWork suffix joined c hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [splitBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (H : Program 1) (M W : Program 2) (count : OTerm α) :
    Nonempty (Derivation body Gamma (splitRow H M W count)) := by
  let theta : Formula (α ⊕ Fin 1) := splitRow H M W (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,splitInstantiate,varBind] using
      (splitZeroRow (body := body) (Gamma := Gamma) H M W)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      H M W (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,splitSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,splitInstantiate,varBind] using (Nonempty.intro h)

theorem successfulSplit (H : Program 1) (M W : Program 2) (count frontWork suffix joined c : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W count joined c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W count frontWork c ⊓ SuccessfulWork H M W count suffix c)) :=
  splitRowApply H M W count frontWork suffix joined c (allRows H M W count) ha hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitProof
