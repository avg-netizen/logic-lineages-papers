module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperatorsSupportProof PositiveArithmeticSchemasProof
open InternalCalculus SourcePresentationSupportProof JointGammaSemanticsCalibrationProof

theorem scalarOperatorTruth (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat)
    (hcal : ContextUniform.Calibrated data n arity) (context : Nat) (P : Nat → Prop) (x : Nat) :
    realize P (SourcePresentation.scalarOperator data).formula ![context,x] ↔
      ContextUniform.encodedScalar n arity context x ∧
        ∀ y, ContextUniform.encodedR n arity context x y → P y := by
  rw [SourcePresentation.scalarOperator,PositiveArithmeticOperatorsProof.accessibilityOperatorTruth,
    (actualCarrierFormulaTruth data n arity hcal context x).1]
  exact and_congr Iff.rfl (forall_congr' (fun y =>
    imp_congr (actualCertificateGraphTruth data n arity hcal context x y).1 Iff.rfl))

theorem multisetOperatorTruth (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat)
    (hcal : ContextUniform.Calibrated data n arity) (context : Nat) (P : Nat → Prop) (x : Nat) :
    realize P (SourcePresentation.multisetOperator data).formula ![context,x] ↔
      ContextUniform.encodedList n arity context x ∧
        ∀ y, ContextUniform.encodedDirect n arity context x y → P y := by
  rw [SourcePresentation.multisetOperator,PositiveArithmeticOperatorsProof.accessibilityOperatorTruth,
    (actualCarrierFormulaTruth data n arity hcal context x).2]
  exact and_congr Iff.rfl (forall_congr' (fun y =>
    imp_congr (actualCertificateGraphTruth data n arity hcal context x y).2 Iff.rfl))

theorem actualClosedSourceOperator : JointGammaSemanticsTargets.ActualClosedSourceOperator := by
  intro data n arity hcal context P x
  constructor
  · rw [closedPresentationTruth,
      (TaggedArithmeticOperatorsProof.taggedBranchIsolation (SourcePresentation.scalarOperator data)
        (SourcePresentation.multisetOperator data) P context x).1]
    exact scalarOperatorTruth data n arity hcal context _ x
  · rw [closedPresentationTruth,
      (TaggedArithmeticOperatorsProof.taggedBranchIsolation (SourcePresentation.scalarOperator data)
        (SourcePresentation.multisetOperator data) P context x).2]
    exact multisetOperatorTruth data n arity hcal context _ x

theorem actualAllTermsFormulaTruth : JointGammaSemanticsTargets.ActualAllTermsFormulaTruth := by
  intro data n arity hcal context P
  rw [SourcePresentation.allTermsFormula,allScalarTruth]
  apply forall_congr'
  intro x
  rw [generalImpTruth,embeddingTruth]
  have hc : FirstOrder.Language.Formula.Realize ((SourcePresentation.checkerFormula data.scalar).subst
      ![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))])
      (Sum.elim Empty.elim (fun _ : Fin 1 => x)) ↔
      ContextUniform.encodedScalar n arity context x := by
    simp only [FirstOrder.Language.Formula.Realize]
    rw [BoundedFormula.realize_subst]
    have hv : (fun a : Fin 2 =>
        (![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))] a).realize
          (Sum.elim Empty.elim (fun _ : Fin 1 => x))) = ![context,x] := by
      funext i
      exact Fin.cases (numeralTruth context _)
        (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [hv]
    exact (actualCarrierFormulaTruth data n arity hcal context x).1
  rw [hc,predicateTruth,PositiveArithmeticTransformsProof.tagTermTruth]
  rfl

theorem actualUniformSourceFormulasExist : JointGammaSemanticsTargets.ActualUniformSourceFormulasExist := by
  intro n arity
  obtain ⟨data,hcal⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  refine ⟨data,hcal,?_⟩
  intro context P
  exact ⟨actualClosedSourceOperator data n arity hcal context P,
    actualAllTermsFormulaTruth data n arity hcal context P⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsProof
