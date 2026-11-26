module
public import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTargets
import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthInactiveProof
import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthSignProof
import LogicLineages.PermittedControl.ActualCanonicalSignFundingProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
open PreparedProjection ActualZeroClassReplacement ActualReadChargeIteration
open ActualCanonicalOperandGrouping ActualCanonicalStoppingTrace ActualCanonicalZeroTrace
open ActualCanonicalTerminalTruth ActualCanonicalSignFunding
open ActualSignedOrdinaryPairHigh (OrderTest)

private theorem linearForward (f ρ : Nat → Nat) (top : Nat) (source stopped : ReadState)
    (xs : List Read) (live : liftedReads f ρ stopped.reads)
    (bounded : ∀ rd ∈ stopped.reads, rd.1.2.rank ≤ top)
    (normal : normalizeCanonical f ρ stopped.reads = some xs)
    (inactive : ¬ ActiveAt top xs) (sameValue : stateValue source = stateValue stopped) :
    LinearForward f ρ top source stopped xs := by
  intro test positive
  have admitted : test.test.Admitted := by cases test <;> trivial
  obtain ⟨scope,someTied,meaning⟩ := exactCanonicalInactiveTruth f ρ top stopped.constant
    stopped.reads xs live bounded normal inactive test.test positive admitted
  refine ⟨scope,someTied,?_⟩
  intro ν tied
  obtain ⟨slots,hits,current,_⟩ := meaning ν tied
  refine ⟨slots,hits,?_⟩
  rw [sameValue]
  exact current

theorem exactFundedForwardTruth : ExactFundedForwardTruth := by
  intro f B chosen ρ strict r top initial stopped answers live ranks long signPaid path stop
  obtain ⟨_,endLive,endRank,_,value,_⟩ := exactCanonicalTraceReplay f B chosen ρ r top
    initial stopped answers path
  obtain ⟨xs,normal,sourceReads,branches⟩ := stop
  refine ⟨xs,normal,sourceReads,?_⟩
  rcases branches with inactive | ⟨active,nonzero⟩
  · exact Or.inl ⟨inactive,linearForward f ρ top initial stopped xs (endLive live)
      (fun rd member => (endRank ranks rd member).2) normal inactive value⟩
  · have localPaid := (exactCanonicalSignFunding f B chosen ρ r top initial stopped answers
      live ranks long path xs normal).2.2 signPaid
    obtain ⟨a,anns,C,matching,aligned,maximum,coeff,notZero,equation,errorBound,
      positiveValue,negativeValue,nonnegativeValue,notZeroValue,tests⟩ :=
      exactCanonicalNonzeroTruth f B chosen ρ strict r top stopped xs
        (endLive live) (endRank ranks) normal nonzero localPaid
    have verdict : NonzeroForward f B ρ r top initial stopped xs := by
      unfold NonzeroForward
      refine ⟨nonzero,localPaid,?_⟩
      refine ⟨a,matching,notZero,?_⟩
      intro test positive
      rw [value]
      exact tests test positive
    exact Or.inr (show ActiveAt top xs ∧ NonzeroForward f B ρ r top initial stopped xs from
      And.intro active verdict)

end LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
