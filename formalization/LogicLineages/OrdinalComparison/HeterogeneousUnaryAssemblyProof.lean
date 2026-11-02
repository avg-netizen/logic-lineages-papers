module
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyMergeProof
public import LogicLineages.OrdinalComparison.SourceUnaryChainProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Proof
open ScalarCarrierAccounting OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem assigned_vectors_unique {Γ}
    (ts : List (OriginalTerm Γ (Ty.curriedGround 1))) (xs ys : List (OrdinalVector Γ 1))
    (hx : List.Forall₂ (fun t v => AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v) ts xs)
    (hy : List.Forall₂ (fun t v => AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v) ts ys) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | @cons t x ts xs htx hrest ih =>
    cases hy with
    | @cons _ y _ ys hty htail =>
      have he : x = y := Option.some.inj (htx.symm.trans hty)
      exact congrArg₂ List.cons he (ih ys htail)

theorem head_sum_calibration {Γ} (vs : List (OrdinalVector Γ 1)) :
    SourceUnaryChain.headSum (fun _ => 1) vs = chargedSum (vs.map (fun v => unitValue (v 1))) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ordinalNaturalSum (ordinalNaturalSum (unitValue (v 1)) 3)
      (SourceUnaryChain.headSum (fun _ => 1) vs) =
      ordinalNaturalSum (unitValue (v 1) + 3) (chargedSum (vs.map (fun v => unitValue (v 1))))
    rw [ih]
    have he : ordinalNaturalSum (unitValue (v 1)) 3 = unitValue (v 1) + 3 := by
      simpa using actualNaturalSumFiniteRight (unitValue (v 1)) 3
    rw [he]

theorem actualMergedChain : Targets.ActualMergedChain := by
  intro Γ ops
  have hmerge := exactMergedAssignments Γ ops
  obtain ⟨ws,hws,v,hv,hvalue⟩ := SourceUnaryChain.Proof.fullSourceUnaryChain (context ops) (terms ops)
  have he : ws = vectors ops := assigned_vectors_unique (terms ops) ws (vectors ops) hws hmerge.2.1
  subst ws
  obtain ⟨v',hv',hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated (context ops)
    (Ty.curriedGround 1) OrdinalSyntax.defaultPolicy (SourceUnaryChain.chainSource (terms ops))
  have hev : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst v'
  refine ⟨v,hv,?_⟩
  intro μ
  calc
    expressionValue (UnitObservation.substitution μ) (v 1) = unitValue (v 1) :=
      UnaryCarrier.Proof.positive_unit_value 1 (v 1) (by decide) (hg 1) μ
    _ = SourceUnaryChain.headSum (fun _ => 1) (vectors ops) := hvalue (fun _ => 1)
    _ = chargedSum ((vectors ops).map (fun v => unitValue (v 1))) := head_sum_calibration _
    _ = chargedSum (ops.map (fun op => unitValue (op.vector 1))) := congrArg chargedSum hmerge.2.2
end LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Proof
