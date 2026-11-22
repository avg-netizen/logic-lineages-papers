module
public import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthTargets
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumRowProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumCodeProof
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
open PreparedProjection MixedSameRankResidue
open ActualCanonicalNormalizedTape ActualReadChargeIteration ActualZeroClassReplacement
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualFullValueMaximalMetadata
open ActualSignedOrdinaryPairHigh (OrderTest)

private theorem orderedTruth (R coef : Int) (nonzero : coef ≠ 0)
    (sign : (0 < R ↔ 0 < coef) ∧ (R < 0 ↔ coef < 0) ∧ (0 ≤ R ↔ 0 < coef) ∧ R ≠ 0)
    (test : OrderTest) (positive : Bool) :
    test.test.atPolarity positive R ↔ test.test.atPolarity positive coef := by
  have actual : test.test.Holds R ↔ test.test.Holds coef := by
    cases test with
    | equalZero =>
        exact ⟨fun impossible => False.elim (sign.2.2.2 impossible),
          fun impossible => False.elim (nonzero impossible)⟩
    | nonnegative =>
        change 0 ≤ R ↔ 0 ≤ coef
        rw [sign.2.2.1]
        omega
    | positive => exact sign.1
  cases positive with
  | false => exact not_congr actual
  | true => exact actual

theorem exactCanonicalNonzeroTruth : ExactCanonicalNonzeroTruth := by
  intro f B selected ρ strict r top s xs live ranked normal stop funded
  obtain ⟨a,anns,C,ν,listed,matching,packet,aligned,maximum,floor,guards,ready,transfer,
    coeff,nonzero,equation⟩ := stop
  let terms := xs.map Prod.fst
  let vals := xs.map Prod.snd
  let parts := rowParts f C terms vals anns
  let R := stateValue s
  let E := s.constant + parts.2
  let coef := maximalCoefficient terms a
  have tape := exactCanonicalTapeCertificate f ρ s.reads xs live normal
  have raws : ∀ t ∈ terms, ρ t.2.rank ≤ ρ top := by
    intro t member
    obtain ⟨rd,here,rfl⟩ := List.mem_map.mp member
    obtain ⟨prior,inRaw,key,_⟩ := (tape.records rd here).2.2
    rw [← key]
    exact strict.monotone (ranked prior inRaw).2
  obtain ⟨member,dominates⟩ := List.max?_eq_some_iff.mp maximum
  have est := (exactSignedDecomposition f B selected ρ (ρ top) C s.constant terms vals anns
    aligned raws member dominates floor).2
  have cutoff : SelectedLeadingSignCutoff.cutoff (slopeBound terms)
      (s.constant.natAbs + offsetBound terms) ≤ ρ top := by
    change rowCutoffCode s.constant (terms.map encodeWeighted) ≤ ρ top at funded
    rw [exactEffectiveCutoff.2 s.constant terms] at funded
    exact funded
  have actual := SelectedLeadingSignCutoff.actualLeadingSign f B selected (ρ top) C
    (slopeBound terms) (s.constant.natAbs + offsetBound terms) coef R E cutoff floor nonzero equation est
  exact ⟨a,anns,C,matching,aligned,maximum,coeff,nonzero,equation,est,
    actual.1,actual.2.1,actual.2.2.1,actual.2.2.2,orderedTruth R coef nonzero actual⟩

end LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
