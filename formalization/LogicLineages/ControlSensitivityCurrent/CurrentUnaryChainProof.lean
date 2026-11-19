module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainSpineProof
public import LogicLineages.OrdinalComparison.SourceUnaryChainAlgebraProof
public import LogicLineages.PermittedControl.SelectedSumValueProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment ParametricSourceSuccessor

/-- Reassociation is used at evaluation of the already existing positive
partial only, never to change the term submitted for a partial. -/
private theorem activeAddValue (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal) (a b c : OrdinalExpression Γ) :
    denoteWith f ν (AdmissiblePartial.three p .activeAdd a b c) =
      ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν a) (denoteWith f ν b)) (denoteWith f ν c) := by
  unfold AdmissiblePartial.three
  rw [LogicLineages.PermittedControl.SelectedSumValueProof.sum_value f Γ 3
    (p.shape .activeAdd 2) (OrdinalSyntax.leftShape 2) _ ν]
  rfl

private theorem headValueOfPartial (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal) (ws : List (OrdinalVector Γ 1)) :
    denoteWith f ν (partialSpine p ws 1) = headSum f ν ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν (w 1)) 1)
      (denoteWith f ν (AdmissiblePartial.three p .activeAdd .one (partialSpine p ws 1) .one)) = _
    rw [activeAddValue]
    change ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν (w 1)) 1)
      (ordinalNaturalSum (ordinalNaturalSum 1 (denoteWith f ν (partialSpine p ws 1))) 1) =
      ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν (w 1)) 3) (headSum f ν ws)
    rw [ih]
    exact SourceUnaryChain.Proof.head_step _ _

theorem headValue : CurrentUnaryChainTargets.HeadValue := by
  intro p f Γ vs
  obtain ⟨ws,hws⟩ := sourceVectors p vs
  obtain ⟨u,hu,_⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow .ground .ground)
    p (SourceUnaryChain.chainSource vs)
  refine ⟨ws,u,hws,hu,?_⟩
  have hb := actualBody p Γ vs ws hws
  have h := hu
  change (assignment p (SourceUnaryChain.chainBody vs)).bind (fun v => abstraction p v) = some u at h
  rw [hb] at h
  change abstraction p (fun _ : Fin 1 => scalarSpine ws) = some u at h
  have hh := finalAbstractionHead p (scalarSpine ws) (partialSpine p ws) u (actualPartial p Γ ws) h
  intro ν
  rw [hh]
  exact headValueOfPartial p f ν ws

theorem commonUnitValue : CurrentUnaryChainTargets.CommonUnitValue := by
  intro p f Γ vs
  obtain ⟨ws,u,hws,hu,h⟩ := headValue p f Γ vs
  exact ⟨ws,u,hws,hu,fun ρ => h (commonUnits ρ)⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain
