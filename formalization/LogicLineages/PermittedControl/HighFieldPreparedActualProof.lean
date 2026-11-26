module
public import LogicLineages.PermittedControl.HighFieldPreparedActualTargets
import LogicLineages.PermittedControl.HighFieldPreparedActualWitnessProof
import LogicLineages.PermittedControl.HighFieldComparisonActualProof
import LogicLineages.PermittedControl.HighFieldComparisonCalibrationProof
import LogicLineages.PermittedControl.HighComparisonLowerParameterDomainProof
import LogicLineages.PermittedControl.HighComparisonLowerParameterCodeProof
import LogicLineages.PermittedControl.ThresholdNumericCalibrationProof
import LogicLineages.PermittedControl.EqualGapCertificateCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open OrdinalComparison FieldComparison
open PreparedProjection

private theorem descriptorStable (F G : LongFieldCode) (ρ : Nat → Nat) (mono : StrictMono ρ)
    (rankF rankG : Nat) :
    highRawComparisonForm F G rankF rankG = highRawComparisonForm F G (ρ rankF) (ρ rankG) := by
  rcases lt_trichotomy rankF rankG with forward | rfl | backward
  · have ordered := mono forward
    simp [highRawComparisonForm,forward,ordered]
  · simp [highRawComparisonForm]
  · have ordered := mono backward
    have notForward : ¬ rankF < rankG := not_lt_of_ge backward.le
    have notOrdered : ¬ ρ rankF < ρ rankG := not_lt_of_ge ordered.le
    simp [highRawComparisonForm,backward,ordered,notForward,notOrdered]

private theorem bothDistinctBounds (B : Nat) (F G : ValueField) (x y : Nat)
    (bound : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ min x y) :
    longFieldDistinctBound B (normalizeShortField F) (normalizeShortField G) ≤ x ∧
    longFieldDistinctBound B (normalizeShortField G) (normalizeShortField F) ≤ y := by
  rw [highFieldComparisonCalibration.2.2.1 B F G] at bound
  let first := longFieldDistinctBound B (normalizeShortField F) (normalizeShortField G)
  let second := longFieldDistinctBound B (normalizeShortField G) (normalizeShortField F)
  have inner : max first second ≤ min x y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans bound)
  exact ⟨(le_max_left _ _).trans (inner.trans (min_le_left _ _)),
    (le_max_right _ _).trans (inner.trans (min_le_right _ _))⟩

private theorem lowerDomain (B : Nat) (F G H : ValueField) (sign x : Nat)
    (encoded : encodeComparisonForm (distinctForm F G) = rawLinearForm sign (longFieldCode H))
    (proper : ProperField H) (bound : longFieldDistinctBound B F G ≤ x) :
    ClosedOrdinaryValueDomain H x := by
  cases chosen : distinctForm F G with
  | const c =>
    rw [chosen] at encoded
    have impossible : (0 : Nat) = 1 := congrArg Prod.fst encoded
    cases impossible
  | linear actualSign actualField =>
    rw [chosen] at encoded
    have reflected := HighComparisonLowerParameter.originalFieldCodeExact.2
      actualSign sign actualField H encoded
    have exactChoice : distinctForm F G = .linear sign H := by
      rw [chosen,reflected.1,reflected.2]
    exact HighComparisonLowerParameter.affordableLowerParameter B F G H sign x exactChoice proper bound

private theorem reverseTwice (wanted : Nat) (admitted : wanted ≤ 2) :
    reverseComparisonCode (reverseComparisonCode wanted) = wanted := by
  rcases (show wanted = 0 ∨ wanted = 1 ∨ wanted = 2 by omega) with rfl | rfl | rfl <;> rfl

private theorem reverseWanted (vF vG wanted : Nat) (admitted : wanted ≤ 2) :
    (numericalComparison vG vF = sortedWanted 1 wanted) ↔ numericalComparison vF vG = wanted := by
  change (numericalComparison vG vF = reverseComparisonCode wanted) ↔ numericalComparison vF vG = wanted
  constructor
  · intro sorted
    have reverse := congrArg reverseComparisonCode sorted
    rw [reverseComparisonCode_correct,reverseTwice wanted admitted] at reverse
    exact reverse
  · intro real
    rw [← reverseComparisonCode_correct vF vG,real]

theorem actualPreparedComparison : ActualPreparedComparison := by
  intro f B selected F G properF properG ρ mono rankF rankG wanted bound
  obtain ⟨vF,vG,actualF,actualG,unique,forward,equal,backward⟩ :=
    highFieldComparisonActual f B selected F G properF properG (ρ rankF) (ρ rankG) bound
  have bounds := bothDistinctBounds B F G (ρ rankF) (ρ rankG) bound
  let R := highRawComparisonForm (longFieldCode F) (longFieldCode G) (ρ rankF) (ρ rankG)
  have prepared : Witness f ρ rankF rankG
      (compile (longFieldCode F,longFieldCode G,rankF,rankG,wanted))
      (numericalComparison vF vG = wanted) := by
    change Witness f ρ rankF rankG (postprocess
      (highRawComparisonForm (longFieldCode F) (longFieldCode G) rankF rankG,rankF,rankG,wanted)) _
    rw [descriptorStable (longFieldCode F) (longFieldCode G) ρ mono rankF rankG]
    change Witness f ρ rankF rankG (postprocess (R,rankF,rankG,wanted)) _
    by_cases admitted : wanted ≤ 2
    · rcases lt_trichotomy rankF rankG with ordered | same | ordered
      · have current : ρ rankF < ρ rankG := mono ordered
        obtain ⟨orientation,meaning⟩ := forward current
        rcases meaning with ⟨answer,raw,result⟩ | ⟨sign,H,h,raw,range,proper,field,printed⟩
        · have exactForm : R = (0,rawConstForm answer) := Prod.ext orientation raw
          rw [exactForm]
          exact constantWitness f ρ 0 answer rankF rankG wanted _ admitted result.symm
        · have exactForm : R = (0,rawLinearForm sign (longFieldCode H)) := Prod.ext orientation raw
          rw [exactForm]
          have sourceCode := (highFieldComparisonCalibration.2.2.2 F G (ρ rankF) (ρ rankG)).1 current
          have sameCode := (congrArg Prod.snd sourceCode).symm.trans raw
          have domain := lowerDomain B (normalizeShortField F) (normalizeShortField G) H
            sign (ρ rankF) sameCode proper bounds.1
          have lowest : lowerRank 0 rankF rankG = min rankF rankG := (min_eq_left ordered.le).symm
          have strict : lowerRank 0 rankF rankG < max rankF rankG := by
            simpa [lowerRank,max_eq_right ordered.le] using ordered
          have positive : 0 < ρ (max rankF rankG) := by
            rw [max_eq_right ordered.le]
            exact Nat.zero_le _ |>.trans_lt current
          have exactRows : InverseTableRows sign (ρ (max rankF rankG)) h vG vF := by
            rw [max_eq_right ordered.le]
            exact printed
          exact linearWitness f ρ 0 sign rankF rankG wanted H h vF vG admitted range
            lowest strict positive domain field exactRows Iff.rfl
      · have exactForm : R = (0,rawConstForm (numericalComparison vF vG)) :=
          equal (congrArg ρ same)
        rw [exactForm]
        exact constantWitness f ρ 0 _ rankF rankG wanted _ admitted rfl
      · have current : ρ rankG < ρ rankF := mono ordered
        obtain ⟨orientation,meaning,flip⟩ := backward current
        have flip' : flipHighComparisonAnswer 1 (numericalComparison vG vF) =
            numericalComparison vF vG := by
          rw [orientation] at flip
          exact flip
        rcases meaning with ⟨answer,raw,result⟩ | ⟨sign,H,h,raw,range,proper,field,printed⟩
        · have exactForm : R = (1,rawConstForm answer) := Prod.ext orientation raw
          rw [exactForm]
          exact constantWitness f ρ 1 answer rankF rankG wanted _ admitted (result ▸ flip')
        · have exactForm : R = (1,rawLinearForm sign (longFieldCode H)) := Prod.ext orientation raw
          rw [exactForm]
          have sourceCode := (highFieldComparisonCalibration.2.2.2 F G (ρ rankF) (ρ rankG)).2.2 current
          have sameCode := (congrArg Prod.snd sourceCode).symm.trans raw
          have domain := lowerDomain B (normalizeShortField G) (normalizeShortField F) H
            sign (ρ rankG) sameCode proper bounds.2
          have lowest : lowerRank 1 rankF rankG = min rankF rankG := (min_eq_right ordered.le).symm
          have strict : lowerRank 1 rankF rankG < max rankF rankG := by
            simpa [lowerRank,max_eq_left ordered.le] using ordered
          have positive : 0 < ρ (max rankF rankG) := by
            rw [max_eq_left ordered.le]
            exact Nat.zero_le _ |>.trans_lt current
          have exactRows : InverseTableRows sign (ρ (max rankF rankG)) h vF vG := by
            rw [max_eq_left ordered.le]
            exact printed
          exact linearWitness f ρ 1 sign rankF rankG wanted H h vG vF admitted range
            lowest strict positive domain field exactRows (reverseWanted vF vG wanted admitted)
    · exact invalidWitness f ρ R rankF rankG wanted _ (lt_of_not_ge admitted)
        (numericalComparison_range vF vG)
  obtain ⟨table,p,compiled,shape,length,tableShape,actual,evaluates⟩ := prepared
  exact ⟨vF,vG,table,p,actualF,actualG,unique,compiled,shape,length,tableShape,actual,evaluates⟩

end LogicLineages.PermittedControl.HighFieldPreparedPacket
