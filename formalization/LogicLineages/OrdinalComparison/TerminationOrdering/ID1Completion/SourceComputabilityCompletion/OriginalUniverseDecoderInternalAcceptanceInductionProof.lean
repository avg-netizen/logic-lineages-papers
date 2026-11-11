module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof OriginalUniverseDecoderInternalAcceptanceRunProof
open OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof OriginalUniverseDecoderInternalAcceptanceInductionCoreProof
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
    (count second frontWork suffix joined initial joinedInitial c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing initial (suc z) frontWork)))
    (hjp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing joinedInitial (suc z) joined))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (add (suc count) second) joined c)) := by
  have hr := successfulWorkAt H M W (suc count) frontWork initial c hp hf
  apply frameCases H M W frontWork suffix joined initial joinedInitial c _ hn ha hp hjp
  · intro β j Delta hj ht _
    have hr' := renameInto hr j Delta hj
    simp only [graph3Rename,numeral,sucRelabel,zRelabel,sucRelabel] at hr'
    have hbad := iterateAfterFirstRecover H M W
      (count.relabel j) (initial.relabel j) z (numeral 2) (c.relabel j) ht hr'
    obtain ⟨hbot⟩ := failureImpossible H M W (count.relabel j) (c.relabel j) hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta frontNext joinedNext nextState joinedNextState hj haNext hpNext hjpNext ht hjt
    simp only [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,addRelabel,sucRelabel]
    have hr' := renameInto hr j Delta hj
    simp only [graph3Rename,numeral,sucRelabel,zRelabel,sucRelabel] at hr'
    have hrow' := renameInto hrow j Delta hj
    rw [appendRowRename] at hrow'
    have hs' := renameInto hs j Delta hj
    rw [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename] at hs'
    have hjp' := renameInto hjp j Delta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hjp'
    have hnext := iterateAfterFirstRecover H M W
      (count.relabel j) (initial.relabel j) nextState (numeral 2) (c.relabel j) ht hr'
    have hdone := successfulWorkIntro H M W (count.relabel j) frontNext nextState (c.relabel j) hpNext hnext
    have hcombined := rowApply H M W (count.relabel j) (second.relabel j)
      frontNext (suffix.relabel j) joinedNext (c.relabel j) hrow' haNext hdone hs'
    have hcombinedRun := successfulWorkAt H M W (add (count.relabel j) (second.relabel j))
      joinedNext joinedNextState (c.relabel j) hjpNext hcombined
    have hrun := iterateAfterFirst H M W
      (add (count.relabel j) (second.relabel j))
      (joinedInitial.relabel j) joinedNextState (numeral 2) (c.relabel j) hjt hcombinedRun
    have hfinish := successfulWorkIntro H M W (suc (add (count.relabel j) (second.relabel j)))
      (joined.relabel j) (joinedInitial.relabel j) (c.relabel j) hjp' hrun
    exact countTransport H M W (suc (add (count.relabel j) (second.relabel j)))
      (add (suc (count.relabel j)) (second.relabel j)) (joined.relabel j) (c.relabel j)
      ⟨symm (leftSuccessor (count.relabel j) (second.relabel j))⟩ hfinish

def stateQueries : Fin 2 → Program 2 :=
  fun i => pairOf (InternalLessThan.constantOne 2) (.projection i)

theorem nonemptyCore (H : Program 1) (M W : Program 2)
    (count second frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (add (suc count) second) joined c)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases stateQueries (Fin.cons frontWork (Fin.cons joined Fin.elim0)) _
  intro β j ys Delta hj hq
  simp only [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  rw [appendRowRename] at hrow'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hf' := renameInto hf j Delta hj
  simp only [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename,sucRelabel] at hf'
  have hs' := renameInto hs j Delta hj
  rw [OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkRename] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  have hp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
    (ys 0) (suc z) (frontWork.relabel j) xs (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)
  have hjp := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (suc z) (joined.relabel j) xs (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 1 xs)
  exact nonemptyAtStates H M W (count.relabel j) (second.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1) (c.relabel j)
    hrow' ha' hf' hs' hn' hp hjp

theorem succCore (H : Program 1) (M W : Program 2) (count second frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (add (suc count) second) joined c)) := by
  apply formulaCases (eqn frontWork z)
  · exact emptyCore H M W (suc count) second frontWork suffix joined c
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · exact nonemptyCore H M W count second frontWork suffix joined c
      (withHyp hrow _) (withHyp ha _) (withHyp hf _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (H : Program 1) (M W : Program 2) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H M W count))) :
    Nonempty (Derivation body Gamma (appendRow H M W (suc count))) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let second : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let c : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 5)
  let A := graph2 append joined frontWork suffix ⊓
    (SuccessfulWork H M W (suc n) frontWork c ⊓ SuccessfulWork H M W second suffix c)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [appendRowRename] at hrow'
  obtain ⟨d⟩ := succCore H M W n second frontWork suffix joined c hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (H : Program 1) (M W : Program 2) (count : OTerm α) :
    Nonempty (Derivation body Gamma (appendRow H M W count)) := by
  let theta : Formula (α ⊕ Fin 1) := appendRow H M W (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,appendInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) H M W)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      H M W (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,appendSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,appendInstantiate,varBind] using (Nonempty.intro h)

theorem successfulAppend (H : Program 1) (M W : Program 2)
    (first second frontWork suffix joined c : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W first frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (add first second) joined c)) :=
  rowApply H M W first second frontWork suffix joined c (allRows H M W first) ha hf hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionProof
