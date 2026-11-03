module
public import LogicLineages.OrdinalComparison.ActualUnaryRayTargets
public import LogicLineages.OrdinalComparison.UnitScalarEvaluationCodeProof
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderProof
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Proof
open AdmissibleAssignment OriginalDomain ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem weaken_value {Γ} (q : OrdinalExpression Γ)
    (ρ : Variable (.ground::Γ) .ground → Nat) :
    expressionValue (UnitObservation.substitution ρ) (ordinalExpressionRename (fun x => .there x) q) =
      expressionValue (UnitObservation.substitution (fun x => ρ (.there x))) q := by
  induction q with
  | var c => rcases c with ⟨σ,x,j⟩;cases σ <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalExpressionRename,substitute,expressionValue,denote] at *
    rw [iha,ihb]

theorem actualSourceRay : Targets.ActualSourceRay := by
  intro Γ K
  obtain ⟨u,c,hu,hclose,hcode,hc,hscalar⟩ :=
    UnitScalarEvaluationCode.Proof.actualClosedSourceScalar Γ (Ty.curriedGround 1) K
  obtain ⟨u',hu',hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround 1) OrdinalSyntax.defaultPolicy K
  have he : u'=u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨a,ha,haeval,haval⟩ := UnitHeadEvaluation.Proof.generatedPositiveEvaluation Γ 1
    (u (UnaryCarrier.headIndex 0)) (hg (UnaryCarrier.headIndex 0)) (by decide)
  let w : OrdinalVector (.ground::Γ) (Ty.curriedGround 1).level := SourceRenaming.renameVector (fun x => .there x)
    (GroundClosing.vector (UnaryCarrier.groundMap Γ) u)
  let z : OrdinalVector (.ground::Γ) Ty.ground.level := fun j => .var ⟨.ground,.here,j⟩
  let v : OrdinalVector (.ground::Γ) Ty.ground.level :=
    application (σ := .ground) (τ := .ground) OrdinalSyntax.defaultPolicy w z
  have hw : assignment OrdinalSyntax.defaultPolicy
      ((UnaryCarrier.closeGround K).rename (fun x => .there x)) = some w := by
    rw [SourceRenaming.Proof.assignmentNaturality,hclose]
    rfl
  have hv : assignment OrdinalSyntax.defaultPolicy (source K) = some v := by
    change (assignment OrdinalSyntax.defaultPolicy ((UnaryCarrier.closeGround K).rename (fun x => .there x))).bind
      (fun f => (assignment OrdinalSyntax.defaultPolicy (.var (.here : Variable (.ground::Γ) .ground))).bind
        (fun g => some (application OrdinalSyntax.defaultPolicy f g))) = some v
    rw [hw]
    rfl
  refine ⟨u,a,c,v,⟨hu,ha,hcode⟩,hv,?_,hscalar,?_⟩
  · intro μ
    exact (UnaryCarrier.Proof.positive_unit_value 1 _ (by decide) (hg (UnaryCarrier.headIndex 0)) μ).trans haval.symm
  · intro ρ
    have hh : expressionValue (UnitObservation.substitution ρ) (w (UnaryCarrier.headIndex 0)) = a.evaluate.1.repr := by
      change expressionValue (UnitObservation.substitution ρ)
        (ordinalExpressionRename (fun x => .there x) (GroundClosing.expression (UnaryCarrier.groundMap Γ) (u (UnaryCarrier.headIndex 0)))) = _
      rw [weaken_value,UnaryCarrier.Proof.ground_close_value]
      exact haval.symm
    have hs : expressionValue (UnitObservation.substitution ρ) (w 0) = (c : Ordinal) := by
      change expressionValue (UnitObservation.substitution ρ)
        (ordinalExpressionRename (fun x => .there x) (GroundClosing.expression (UnaryCarrier.groundMap Γ) (u 0))) = _
      rw [weaken_value]
      exact hscalar _
    have happ := SourceAnnotationBuilder.Proof.application_scalar (n := 0) w z
    refine (congrArg (expressionValue (UnitObservation.substitution ρ)) happ).trans ?_
    change (actualCollapse (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (expressionValue (UnitObservation.substitution ρ) (w (UnaryCarrier.headIndex 0))))
      (ordinalNaturalSum (expressionValue (UnitObservation.substitution ρ) (w 0))
        (valuation (UnitObservation.substitution ρ) ⟨.ground,.here,0⟩))) : Ordinal) = _
    rw [hh,hs,(UnitObservation.Proof.groundValue (.ground::Γ) ρ .here).2,
      LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.naturalSum_finite,
      actualNaturalSumFiniteRight]
    have hn : c+(ρ .here+1)=c+1+ρ .here := by omega
    rw [hn]
    unfold rayValue totalNorm actualHeadValue actualHeadInitial
    have hsub : actualOrdinalNorm (fixedHead a)+c+1+ρ .here-actualOrdinalNorm (fixedHead a)=c+1+ρ .here := by omega
    rw [hsub]
    rfl
end LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Proof
