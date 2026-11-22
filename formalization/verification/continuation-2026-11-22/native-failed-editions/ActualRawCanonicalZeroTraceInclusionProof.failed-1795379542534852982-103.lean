module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusionTargets
import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesProof
import LogicLineages.PermittedControl.ActualRawCanonicalZeroReplayProof
import LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixesProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof
import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsEnumProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import Mathlib.Data.List.Forall2

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusion
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualRawCanonicalZeroReplay (AnswerCode SequenceCode encodeAnswers stepCode exactRawCanonicalZeroStep)
open ActualRawCanonicalZeroPrefixes (CandidatePath available prefixes exactRawZeroPrefixEnumeration)
open ActualRawCanonicalAnswerTapes (candidateTapes exactCanonicalAnswerPairs)
open ActualCanonicalZeroTrace (CanonicalZeroWitness CanonicalTrace eraseState exactCanonicalZeroReplay exactCanonicalTraceReplay)
open ActualCanonicalStoppingTrace (StopsAt exactFundedCanonicalStoppingTrace)
open ActualCanonicalOperandGrouping (encodeTerm groupRaw groupTyped exactCanonicalReads)
open ActualWeightedReadNormalization (exactNormalizedReads)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs patterns exactFinitePatternEnumeration)
open ActualReadChargeIteration (ReadState stateCharge)
open ActualFiniteGlobalTail (syntaxOf)
open ActualSyntaxChargeBudget (syntaxBudgetCode syntaxBudget exactChargeBudget budgetCodeExact)
open MixedSameRankResidue (encodeWeighted)

theorem exactActualZeroCandidateEdge : ExactActualZeroCandidateEdge := by
  intro f B selected ρ r top source target answer witness
  have actualStep := (exactCanonicalZeroReplay f B selected ρ r top source target answer witness).1
  refine ⟨?_,?_⟩
  · obtain ⟨xs,anns,C,moved,ledger,x,q,prepared,_⟩ := witness
    obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ source.reads).2 prepared.live
    obtain ⟨out,found,_,tapeEq,_,_⟩ := (exactCanonicalReads f ρ source.reads).2 old legacy
    have same : out = xs := Option.some.inj (found.symm.trans prepared.grouped)
    have frames : xs.map Prod.fst = groupTyped (source.reads.map Prod.fst) :=
      (congrArg (fun ys => ys.map Prod.fst) same).symm.trans tapeEq
    have width : answer.length = (pairs (labels (groupTyped (source.reads.map Prod.fst)))).length := by
      have h := (List.Forall₂.length_eq prepared.matched).symm
      simpa only [frames] using h
    have listEq := (exactCanonicalAnswerPairs.2 (source.reads.map Prod.fst)).2
    change answer.map Answer.code ∈
      candidateTapes (groupRaw ((source.reads.map Prod.fst).map encodeTerm))
    rw [listEq]
    exact List.mem_map.mpr
      ⟨answer,(exactFinitePatternEnumeration _ answer).mpr width,rfl⟩
  · rw [exactRawCanonicalZeroStep,actualStep] <;> rfl

private theorem firstThenPath (start mid endState : RawSyntax) (head : AnswerCode)
    (answers : SequenceCode) (allowed : head ∈ available start)
    (first : stepCode (start,head) = some mid) (tail : CandidatePath mid answers endState) :
    CandidatePath start (head::answers) endState := by
  induction tail with
  | nil => exact CandidatePath.snoc CandidatePath.nil allowed first
  | snoc _ permitted ok ih => exact CandidatePath.snoc ih permitted ok

private theorem actualPath
    (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (r top : Nat) (source target : ReadState) (answers : List (List Answer))
    (witness : CanonicalTrace f B ρ r top answers source target) :
    CandidatePath (encodeSyntax (eraseState source)) (encodeAnswers answers)
        (encodeSyntax (eraseState target)) := by
  induction witness with
  | nil source => exact CandidatePath.nil
  | @cons a tail source mid target step remaining ih =>
    have h := exactActualZeroCandidateEdge f B selected ρ r top source mid a step
    exact firstThenPath _ _ _ _ _ h.1 h.2 ih

theorem exactActualCanonicalCandidateTrace : ExactActualCanonicalCandidateTrace := by
  intro f B selected ρ r top source target answers witness
  have path := actualPath f B selected ρ r top source target answers witness
  have cost := (exactCanonicalTraceReplay f B selected ρ r top source target answers witness).2.2.2.2.2
  have length : (encodeAnswers answers).length ≤ stateCharge r source := by
    simp only [encodeAnswers,List.length_map]
    omega
  exact ⟨path,(exactRawZeroPrefixEnumeration _ _ _).mpr ⟨path,length⟩⟩

theorem exactActualCanonicalBudgetInclusion : ExactActualCanonicalBudgetInclusion := by
  intro f B selected ρ r top source target answers witness
  have precise := (exactActualCanonicalCandidateTrace f B selected ρ r top source target answers witness).2
  have actual := (exactRawZeroPrefixEnumeration _ _ _).mp precise
  have bound : stateCharge r source ≤ syntaxBudgetCode r (encodeSyntax (eraseState source)).2 := by
    change stateCharge r source ≤ syntaxBudgetCode r ((syntaxOf source).map encodeWeighted)
    rw [budgetCodeExact.2]
    exact exactChargeBudget.1 r source
  exact (exactRawZeroPrefixEnumeration _ _ _).mpr ⟨actual.1,actual.2.trans bound⟩

theorem exactFundedStoppingCandidateInclusion : ExactFundedStoppingCandidateInclusion := by
  intro f B selected ρ strict r top source live ranks long transfer comparison
  obtain ⟨answers,rawAnswers,target,witness,stop,_⟩ :=
    exactFundedCanonicalStoppingTrace f B selected ρ strict r top source live ranks long transfer comparison
  exact ⟨answers,target,witness,stop,
    exactActualCanonicalBudgetInclusion f B selected ρ r top source target answers witness⟩

end LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusion
