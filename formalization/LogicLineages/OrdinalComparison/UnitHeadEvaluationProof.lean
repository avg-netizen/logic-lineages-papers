module
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationTargets
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationProof
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
public import LogicLineages.OrdinalComparison.EncodedDescentProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation.Proof
open ForwardTranslation ScalarAnnotationData OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem unit_value {Γ} (q : OrdinalExpression Γ) (ν : OrdinalComponent Γ → Ordinal) :
    denote ν (unitSyntax q) = denote (fun _ => 1) q := by
  induction q with
  | var c | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [unitSyntax,denote]
    rw [iha,ihb]

theorem extract_total {Γ i q} (hg : GeneratedOrdinalGrade Γ i q) (hi : 0 < i) :
    ∃ a : ClosedPositive, extractUnitHead q = some a := by
  induction hg with
  | one i => exact ⟨.one,rfl⟩
  | omega i hp => exact ⟨.omega,rfl⟩
  | var x j => exact ⟨.one,rfl⟩
  | add hf hg ihf ihg =>
    obtain ⟨a,ha⟩ := ihf hi
    obtain ⟨b,hb⟩ := ihg hi
    change extractPositive (unitSyntax _) = some a at ha
    change extractPositive (unitSyntax _) = some b at hb
    exact ⟨.add a b,by simp [extractUnitHead,unitSyntax,extractPositive,ha,hb]⟩
  | emul hp hf hg ihf ihg =>
    obtain ⟨a,ha⟩ := ihf (by omega)
    obtain ⟨b,hb⟩ := ihg hi
    change extractPositive (unitSyntax _) = some a at ha
    change extractPositive (unitSyntax _) = some b at hb
    exact ⟨.emul a b,by simp [extractUnitHead,unitSyntax,extractPositive,ha,hb]⟩
  | collapse hf hg ihf ihg => omega

theorem generatedPositiveEvaluation : Targets.GeneratedPositiveEvaluation := by
  intro Γ i q hg hi
  obtain ⟨a,ha⟩ := extract_total hg hi
  refine ⟨a,ha,?_,?_⟩
  · simp [evaluateUnitHead,ha]
  · exact (closedPositiveEvaluationSound Γ (unitSyntax q) a ha (fun _ => 1)).trans
      (unit_value q (fun _ => 1))

theorem exactNumericBridge : Targets.ExactNumericBridge := by
  have hn : Primrec normalCode := encodedClosedPositivePrimitiveRecursive
  have hf : Primrec finiteCode := encodedFiniteAlgorithmsPrimitiveRecursive.1.comp hn
  have hv : Primrec finiteValueCode :=
    (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).comp hn
  refine ⟨hn,hf,hv,?_⟩
  intro a
  have he : normalCode (closedPositiveCode a) = rawNoteEncode a.evaluate.1 :=
    encodedClosedPositiveCorrect a
  refine ⟨he,?_,?_⟩
  · change encodedFiniteTest (normalCode _) = true ↔ _
    rw [he]
    exact (encodedFiniteCorrect a.evaluate).1
  · change encodedFiniteTest (normalCode _) = true → _
    change encodedFiniteTest (normalCode _) = true →
      (encodedFiniteValue (normalCode _) : Ordinal) = _
    rw [he]
    exact (encodedFiniteCorrect a.evaluate).2

theorem actualOperatorClassification : Targets.ActualOperatorClassification := by
  intro Γ op hop
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ _ OrdinalSyntax.defaultPolicy op.source
  have he : u = op.vector := Option.some.inj (hu.symm.trans hop)
  subst u
  have hgrade := hg (UnaryCarrier.headIndex op.arity)
  obtain ⟨a,ha,hev,hval⟩ := generatedPositiveEvaluation Γ 1 op.head hgrade (by decide)
  have hn := exactNumericBridge.2.2.2 a
  have hfinite : finiteCode (closedPositiveCode a) = true ↔ denote (fun _ => 1) op.head < Ordinal.omega0 := by
    rw [← hval]
    exact hn.2.1
  refine ⟨a,ha,hev,hval,hfinite,?_,?_,?_⟩
  · constructor
    · intro h
      apply le_of_not_gt
      intro hlt
      have ht := hfinite.mpr hlt
      rw [h] at ht
      contradiction
    · intro h
      cases hb : finiteCode (closedPositiveCode a) with
      | false => rfl
      | true => exact False.elim ((not_lt_of_ge h) (hfinite.mp hb))
  · intro hf
    exact (hn.2.2 hf).trans hval
  · intro μ
    exact hval.trans (UnaryCarrier.Proof.positive_unit_value 1 op.head (by decide) hgrade μ).symm
end LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation.Proof
