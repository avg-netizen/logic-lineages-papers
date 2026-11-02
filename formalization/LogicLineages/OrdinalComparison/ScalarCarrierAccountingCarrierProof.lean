module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingTargets
public import LogicLineages.OrdinalComparison.SelectedAffineHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
open OriginalDomain AdditiveHeadTree

theorem carrier_grade (label : Carrier) : ∀ j, GeneratedOrdinalGrade label.context j.val (label.vector j) := by
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated label.context
    (Ty.curriedGround 1) OrdinalSyntax.defaultPolicy label.term
  have he : u = label.vector := Option.some.inj (hu.symm.trans label.assigned)
  subst u
  exact hg

/-- The all-one label value is the actual common functional unit observation,
for every ground environment; derived from its actual generated assignment. -/
theorem carrier_common_unit (label : Carrier) (μ : Variable label.context .ground → Nat) :
    expressionValue (UnitObservation.substitution μ) (label.vector 1) = label.head := by
  exact UnaryCarrier.Proof.positive_unit_value 1 (label.vector 1) (by decide)
    (carrier_grade label 1) μ

theorem carrier_for_operator {k Γ}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h)
    (op : GroundOperatorDischarge.OperatorWitness OrdinalSyntax.defaultPolicy h) :
    ∃ label : Carrier, label.head = unitValue h := by
  obtain ⟨r,t,u,hu,hh⟩ := op
  obtain ⟨u',w,v,hu',hw,hv,heq,hscalar,hvalue⟩ := UnaryCarrier.Proof.actualCarrier Γ k r t
  have heu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  let label : Carrier :=
    { context := Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ
      term := UnaryCarrier.carrier t
      vector := v
      assigned := hv
      noGround := UnaryCarrier.Proof.carrier_no_ground t }
  refine ⟨label,?_⟩
  have hval : expressionValue (UnitObservation.substitution (fun _ => 0)) (label.vector 1) =
      expressionValue (UnitObservation.substitution (fun _ => 0)) h := by
    simpa only [hh] using hvalue (fun _ => 0) (fun _ => 0)
  calc
    label.head = expressionValue (UnitObservation.substitution (fun _ => 0)) (label.vector 1) :=
      (carrier_common_unit label (fun _ => 0)).symm
    _ = expressionValue (UnitObservation.substitution (fun _ => 0)) h := hval
    _ = unitValue h := UnaryCarrier.Proof.positive_unit_value 1 h (by decide)
      (AdditiveHeadTree.Proof.head_grade ht) (fun _ => 0)
end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
