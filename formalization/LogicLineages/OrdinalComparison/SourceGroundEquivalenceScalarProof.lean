module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionProof
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof
open OriginalDomain SourceCollisionCompletion
open SourceCollisionCompletion.Proof SourceAdditionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

attribute [local irreducible] Phi actualCollapse

def three {Γ} : OrdinalExpression Γ := .add (.add .one .one) .one
def five {Γ} : OrdinalExpression Γ := .add (.add (.add .one .one) (.add .one .one)) .one

theorem identity_application {Γ} (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.app identity t)=
      some (fun _ => .collapse .one (.add three (v 0))) := by
  change (AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy identity >>= fun f =>
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t >>= fun a =>
      some (AdmissibleAssignment.application OrdinalSyntax.defaultPolicy f a)) = _
  rw [hv]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp only [Ty.level,List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [AdmissibleAssignment.application,AdmissibleAssignment.box,Ty.level,Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega,dite_false]
  simp [Fin.cases_zero,three,AdmissibleAssignment.boxTail,Ty.level,ordinalVectorAt,
    ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,
    ordinalHeadClosure,ordinalHeadClosureComponent,substitute,AdmissibleAssignment.repeated,
    OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,AdmissibleSum.expand]
  all_goals repeat' constructor

theorem constant_application {Γ} (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.app constant t)=
      some (fun _ => .collapse .one (.add five (v 0))) := by
  change (AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy constant >>= fun f =>
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t >>= fun a =>
      some (AdmissibleAssignment.application OrdinalSyntax.defaultPolicy f a)) = _
  rw [hv]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp only [Ty.level,List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [AdmissibleAssignment.application,AdmissibleAssignment.box,Ty.level,Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega,dite_false]
  simp [Fin.cases_zero,five,AdmissibleAssignment.boxTail,Ty.level,ordinalVectorAt,
    ordinalPartialSize,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,
    ordinalFreePartialVector,ordinalHeadClosure,ordinalHeadClosureComponent,substitute,
    AdmissibleAssignment.repeated,OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,
    OrdinalSyntax.leftShape,AdmissibleSum.expand]
  all_goals repeat' constructor

theorem three_value {Γ} (ν : OrdinalComponent Γ → Ordinal) : denote ν three=(3 : Ordinal) := by
  have h1 : denote ν (.one : OrdinalExpression Γ)=((1:Nat):Ordinal) := by simp [denote]
  have h2 := add_value ν _ _ _ _ h1 h1
  exact add_value ν _ _ 2 1 h2 h1
theorem five_value {Γ} (ν : OrdinalComponent Γ → Ordinal) : denote ν five=(5 : Ordinal) := by
  have h1 : denote ν (.one : OrdinalExpression Γ)=((1:Nat):Ordinal) := by simp [denote]
  have h2 := add_value ν _ _ _ _ h1 h1
  have h4 := add_value ν _ _ 2 2 h2 h2
  exact add_value ν _ _ 4 1 h4 h1

theorem identity_raw {Γ} (t : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ) :
    rawScalar (valuation ρ) (.app identity t)=g (rawScalar (valuation ρ) t+3) := by
  obtain ⟨v,hv,hs⟩ := actualScalarTotal Γ t
  apply raw_of_assignment _ _ _ _ (identity_application t v hv)
  have h := add_value (valuation ρ) _ _ 3 _ (three_value _) (hs ρ).1
  have hc := collapse_one_value (valuation ρ) _ _ h
  simpa only [g_calibration,Nat.add_comm 3] using hc

theorem constant_raw {Γ} (t : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ) :
    rawScalar (valuation ρ) (.app constant t)=g (rawScalar (valuation ρ) t+5) := by
  obtain ⟨v,hv,hs⟩ := actualScalarTotal Γ t
  apply raw_of_assignment _ _ _ _ (constant_application t v hv)
  have h := add_value (valuation ρ) _ _ 5 _ (five_value _) (hs ρ).1
  have hc := collapse_one_value (valuation ρ) _ _ h
  simpa only [g_calibration,Nat.add_comm 5] using hc

theorem zero_raw {Γ} (ρ : AdmissibleSubstitution Γ) : rawScalar (valuation ρ) (.zeroC : OriginalTerm Γ .ground)=1 :=
  raw_of_assignment _ _ (fun _ => .one) 1 rfl (by simp [denote])
theorem magnify_raw {Γ} (t : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ) :
    rawScalar (valuation ρ) (magnify t)=g (3*rawScalar (valuation ρ) t+3) := by
  unfold magnify
  rw [actualGroundEraser,zero_raw]
end LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof
