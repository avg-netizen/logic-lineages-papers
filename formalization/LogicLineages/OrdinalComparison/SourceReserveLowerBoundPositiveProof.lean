module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundTargets
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
open OriginalDomain ScalarCarrierAccounting

theorem positive_generated_ambient {Γ i} {h : OrdinalExpression Γ}
    (hg : GeneratedOrdinalGrade Γ i h) (hi : 0 < i) : AmbientGrade Γ i h := by
  induction hg with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | var x j => exact .var x j
  | add _ _ iha ihb => exact .add (iha hi) (ihb hi)
  | emul hpos _ _ iha ihb => exact .emul hpos (iha (by omega)) (ihb hpos)
  | collapse _ _ _ _ => omega

theorem positiveHeadValue : Targets.PositiveHeadValue := by
  intro Γ i h hi hg
  have hp := originalAmbientGradePositive Γ i h (positive_generated_ambient hg hi)
    (UnitObservation.substitution (fun _ => 0))
  rw [UnaryCarrier.Proof.positive_unit_value i h hi hg (fun _ => 0)] at hp
  exact Order.one_le_iff_pos.mpr hp

end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
