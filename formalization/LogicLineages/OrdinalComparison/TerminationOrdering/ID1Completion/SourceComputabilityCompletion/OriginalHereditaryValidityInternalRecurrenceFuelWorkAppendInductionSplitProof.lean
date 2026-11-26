module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitSyntaxProof OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitCoreProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendFrameProof
open InternalNumericIterationProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonemptyAtStates (s t m : Program 2)
    (count frontWork suffix joined initial joinedInitial : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow s t m count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m (suc count) joined)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hp : Nonempty (Derivation body Gamma (StateGraph initial (numeral 1) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (StateGraph joinedInitial (numeral 1) joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (suc count) frontWork ⊓ SuccessfulWork s t m (suc count) suffix)) := by
  have hr := successfulWorkAt s t m (suc count) joined joinedInitial hjp hs
  apply frameCases s t m frontWork suffix joined initial joinedInitial _ hn ha hp hjp
  · intro β j Delta hj _ ht
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hr'
    have hbad := iterateAfterFirstRecover s t m
      (count.relabel j) (joinedInitial.relabel j) z (numeral 2) ht hr'
    obtain ⟨hbot⟩ := failureImpossible s t m (count.relabel j) hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta frontNext joinedNext nextState joinedNextState hj haNext hpNext hjpNext ht hjt
    simp only [conjunctionRename,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkRename,sucRelabel]
    have hr' := renameInto hr j Delta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hr'
    have hrow' := renameInto hrow j Delta hj
    rw [splitRowRename] at hrow'
    have hp' := renameInto hp j Delta hj
    simp only [StateGraph,graph2Rename,oneRename] at hp'
    have hnext := iterateAfterFirstRecover s t m
      (count.relabel j) (joinedInitial.relabel j) joinedNextState (numeral 2) hjt hr'
    have hdone := successfulWorkIntro s t m (count.relabel j) joinedNext joinedNextState hjpNext hnext
    have hsplit := splitRowApply s t m (count.relabel j)
      frontNext (suffix.relabel j) joinedNext hrow' haNext hdone
    have hfRun := successfulWorkAt s t m (count.relabel j)
      frontNext nextState hpNext (OriginalLambdaConstructorGraphSyntaxProof.andLeft hsplit)
    have hrun := iterateAfterFirst s t m
      (count.relabel j) (initial.relabel j) nextState (numeral 2) ht hfRun
    have hfront := successfulWorkIntro s t m (suc (count.relabel j))
      (frontWork.relabel j) (initial.relabel j) hp' hrun
    have hpad := successPadding s t m (count.relabel j) (suc z) (suffix.relabel j) (OriginalLambdaConstructorGraphSyntaxProof.andRight hsplit)
    have he : Derivation body Delta (eqn (add (count.relabel j) (suc z)) (suc (count.relabel j))) :=
      trans (addSucc (count.relabel j) z) (congSuc (addZero (count.relabel j)))
    exact OriginalLambdaConstructorGraphSyntaxProof.andIntro hfront (countTransport s t m (add (count.relabel j) (suc z))
      (suc (count.relabel j)) (suffix.relabel j) ⟨he⟩ hpad)

def stateQueries : Fin 2 → Program 2 :=
  fun i => pairOf (InternalLessThan.constantOne 2) (.projection i)

theorem nonemptyCore (s t m : Program 2)
    (count frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow s t m count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m (suc count) joined)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (suc count) frontWork ⊓ SuccessfulWork s t m (suc count) suffix)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases stateQueries (Fin.cons frontWork (Fin.cons joined Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [conjunctionRename,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  rw [splitRowRename] at hrow'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Delta hj
  simp only [OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkRename,sucRelabel] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  have hp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
    (ys 0) (suc z) (frontWork.relabel j) xs (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)
  have hjp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (suc z) (joined.relabel j) xs (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 1 xs)
  exact nonemptyAtStates s t m (count.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1)
    hrow' ha' hs' hn' hp hjp

theorem succCore (s t m : Program 2) (count frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow s t m count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m (suc count) joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (suc count) frontWork ⊓ SuccessfulWork s t m (suc count) suffix)) := by
  apply formulaCases (eqn frontWork z)
  · exact splitEmptyCore s t m (suc count) frontWork suffix joined
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · exact nonemptyCore s t m count frontWork suffix joined
      (withHyp hrow _) (withHyp ha _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (s t m : Program 2) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow s t m count))) :
    Nonempty (Derivation body Gamma (splitRow s t m (suc count))) := by
  unfold splitRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let frontWork : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let suffix : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := graph2 append joined frontWork suffix ⊓ SuccessfulWork s t m (suc n) joined
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [splitRowRename] at hrow'
  obtain ⟨d⟩ := succCore s t m n frontWork suffix joined hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [splitBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (s t m : Program 2) (count : OTerm α) :
    Nonempty (Derivation body Gamma (splitRow s t m count)) := by
  let theta : Formula (α ⊕ Fin 1) := splitRow s t m (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,splitInstantiate,varBind] using
      (splitZeroRow (body := body) (Gamma := Gamma) s t m)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      s t m (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,splitSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,splitInstantiate,varBind] using (Nonempty.intro h)

theorem successfulSplit (s t m : Program 2) (count frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m count joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m count frontWork ⊓ SuccessfulWork s t m count suffix)) :=
  splitRowApply s t m count frontWork suffix joined (allRows s t m count) ha hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitProof
