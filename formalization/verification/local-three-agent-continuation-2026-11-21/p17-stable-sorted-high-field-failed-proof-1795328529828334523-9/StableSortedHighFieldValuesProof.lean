module
public import LogicLineages.PermittedControl.StableSortedHighFieldTargets
import LogicLineages.PermittedControl.HighFieldComparisonActualProof
import LogicLineages.PermittedControl.HighFieldComparisonCalibrationProof
import LogicLineages.PermittedControl.HighComparisonLowerParameterDomainProof
import LogicLineages.PermittedControl.HighComparisonLowerParameterCodeProof
import LogicLineages.PermittedControl.InverseComparisonPreparedRowsSemanticProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.PermittedControl.FieldComparisonProof
import LogicLineages.PermittedControl.EqualGapCertificateCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open OrdinalComparison FieldComparison PreparedProjection HighFieldPreparedPacket
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem compareAt (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (F G : ValueField) (properF : ProperField F) (properG : ProperField G)
    (x z : Nat) (ordered : x < z)
    (bound : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ x) :
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G z vG ∧
      (∀ u v : Nat, FieldValue f F x u → FieldValue f G z v → u = vF ∧ v = vG) ∧
      match distinctForm (normalizeShortField F) (normalizeShortField G) with
      | .const answer => numericalComparison vF vG = answer
      | .linear sign H =>
        sign ≤ 2 ∧ ProperField H ∧ ∃ h : Nat, FieldValue f H x h ∧ InverseTableRows sign z h vG vF := by
  have common : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ min x z := by
    rwa [min_eq_left ordered.le]
  obtain ⟨vF,vG,actualF,actualG,unique,forward,_,_⟩ :=
    highFieldComparisonActual f B selected F G properF properG x z common
  have raw := (forward ordered).2
  have exactCode := congrArg Prod.snd ((highFieldComparisonCalibration.2.2.2 F G x z).1 ordered)
  rw [exactCode] at raw
  refine ⟨vF,vG,actualF,actualG,unique,?_⟩
  cases form : distinctForm (normalizeShortField F) (normalizeShortField G) with
  | const answer =>
    rw [form] at raw
    rcases raw with ⟨c,same,result⟩ | ⟨_,_,_,same,_,_,_,_⟩
    · have equal : answer = c := congrArg (fun c : RawComparisonFormCode => c.2.1) same
      exact result.trans equal.symm
    · have impossible : (0 : Nat) = 1 := congrArg Prod.fst same
      cases impossible
  | linear sign H =>
    rw [form] at raw
    rcases raw with ⟨_,same,_⟩ | ⟨s,J,h,same,range,proper,actual,table⟩
    · have impossible : (1 : Nat) = 0 := congrArg Prod.fst same
      cases impossible
    · obtain ⟨rfl,rfl⟩ := HighComparisonLowerParameter.originalFieldCodeExact.2 sign s H J same
      exact ⟨range,proper,h,actual,table⟩

private theorem selectedDomain (B : Nat) (F G H : ValueField) (sign x : Nat)
    (bound : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ x)
    (form : distinctForm (normalizeShortField F) (normalizeShortField G) = .linear sign H)
    (proper : ProperField H) : ClosedOrdinaryValueDomain H x := by
  rw [highFieldComparisonCalibration.2.2.1 B F G] at bound
  have leaf : longFieldDistinctBound B (normalizeShortField F) (normalizeShortField G) ≤
      highFieldComparisonBound B F G :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact HighComparisonLowerParameter.affordableLowerParameter B
    (normalizeShortField F) (normalizeShortField G) H sign x form proper (leaf.trans bound)

theorem baseMeaning (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (F G : ValueField) (properF : ProperField F) (properG : ProperField G)
    (ρ : Nat → Nat) (lowRank highRank wanted : Nat)
    (bound : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ ρ lowRank)
    (ν : Nat → Nat) (tied : PreparedTableTied f highRank ρ (basePacket F G lowRank wanted).1 ν)
    (ordered : ρ lowRank < ν 0) :
    (basePacket F G lowRank wanted).2.eval ν ↔ actualOutcome f F G (ρ lowRank) (ν 0) wanted := by
  obtain ⟨vF,vG,actualF,actualG,unique,meaning⟩ :=
    compareAt f B selected F G properF properG (ρ lowRank) (ν 0) ordered bound
  have source : actualOutcome f F G (ρ lowRank) (ν 0) wanted ↔ numericalComparison vF vG = wanted := by
    constructor
    · rintro ⟨u,v,readF,readG,result⟩
      obtain ⟨rfl,rfl⟩ := unique u v readF readG
      exact result
    · intro result
      exact ⟨vF,vG,actualF,actualG,result⟩
  rw [source]
  by_cases admitted : wanted ≤ 2
  · cases form : distinctForm (normalizeShortField F) (normalizeShortField G) with
    | const answer =>
      rw [form] at meaning
      have fixed : numericalComparison vF vG = answer := meaning
      by_cases equals : answer = wanted <;>
        simp [basePacket,admitted,form,constantFormula,flipHighComparisonAnswer,
          fixed,equals,NormalForm.Formula.eval]
    | linear sign H =>
      rw [form] at meaning
      obtain ⟨range,proper,h,actual,table⟩ := meaning
      have sourceTie : PreparedTableTied f highRank ρ [.ordinary lowRank H] ν := by
        simpa [basePacket,admitted,form] using tied
      have actualAssigned : FieldValue f H (ρ lowRank) (ν 1) := (sourceTie 0 (by simp)).2.2
      have same := fieldValueUnique f H _ (ν 1) h actualAssigned actual
      have current : InverseTableRows sign (ν 0) (ν 1) vG vF := by rwa [same]
      have positive : 0 < ν 0 := (Nat.zero_le _).trans_lt ordered
      simpa [basePacket,admitted,form] using
        InverseComparisonPreparedRows.actualInverseRows sign wanted vF vG ν range positive current
  · have impossible : numericalComparison vF vG ≠ wanted :=
      fun h => admitted (h ▸ numericalComparison_range vF vG)
    simp [basePacket,admitted,impossible,NormalForm.Formula.eval]

theorem baseActualReads (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (F G : ValueField) (properF : ProperField F) (properG : ProperField G)
    (ρ : Nat → Nat) (lowRank highRank wanted : Nat) (rankOrder : lowRank < highRank)
    (bound : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ ρ lowRank) :
    let table := (basePacket F G lowRank wanted).1
    ∃ ν : Nat → Nat, PreparedTableTied f highRank ρ table ν ∧
      ∀ (j : Nat) (used : j < table.length),
        lowerOperandRead f ρ (table.get ⟨j,used⟩) = some (some (ν (j+1))) := by
  by_cases admitted : wanted ≤ 2
  · cases form : distinctForm (normalizeShortField F) (normalizeShortField G) with
    | const answer =>
      refine ⟨fun _ => 0,?_,?_⟩
      · intro j used
        simp [basePacket,admitted,form] at used
      · intro j used
        simp [basePacket,admitted,form] at used
    | linear sign H =>
      obtain ⟨_,_,_,_,_,meaning⟩ := compareAt f B selected F G properF properG (ρ lowRank)
        (ρ lowRank + 1) (Nat.lt_succ_self _) bound
      rw [form] at meaning
      obtain ⟨_,proper,h,actual,_⟩ := meaning
      have domain := selectedDomain B F G H sign (ρ lowRank) bound form proper
      have read := (((closedOrdinaryValueActual f H (ρ lowRank)).2 domain).1 h).mpr actual
      have table : (basePacket F G lowRank wanted).1 = [.ordinary lowRank H] := by
        simp [basePacket,admitted,form]
      have witness (ops : List LowerOperand) (one : ops = [.ordinary lowRank H]) :
          ∃ ν : Nat → Nat, PreparedTableTied f highRank ρ ops ν ∧
            ∀ (j : Nat) (used : j < ops.length),
              lowerOperandRead f ρ (ops.get ⟨j,used⟩) = some (some (ν (j+1))) := by
        subst ops
        refine ⟨fun _ => h,?_,?_⟩
        · intro j used
          have length : j < 1 := used
          have zero : j = 0 := by omega
          subst j
          exact ⟨rankOrder,domain,actual⟩
        · intro j used
          have length : j < 1 := used
          have zero : j = 0 := by omega
          subst j
          exact read
      exact witness _ table
  · refine ⟨fun _ => 0,?_,?_⟩
    · intro j used
      simp [basePacket,admitted] at used
    · intro j used
      simp [basePacket,admitted] at used

end LogicLineages.PermittedControl.StableSortedHighField
