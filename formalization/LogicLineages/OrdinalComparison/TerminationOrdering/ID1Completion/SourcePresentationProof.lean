module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperatorsSupportProof PositiveArithmeticSchemasProof
open InternalCalculus SourcePresentation SourcePresentationSupportProof

theorem actualClosedSourceOperator : SourcePresentationTargets.ActualClosedSourceOperator := by
  intro data n arity Gamma hcal context P x
  constructor
  · rw [closedPresentationTruth,
      (TaggedArithmeticOperatorsProof.taggedBranchIsolation (SourcePresentation.scalarOperator data)
        (SourcePresentation.multisetOperator data) P context x).1]
    exact scalarOperatorTruth data n arity Gamma hcal context _ x
  · rw [closedPresentationTruth,
      (TaggedArithmeticOperatorsProof.taggedBranchIsolation (SourcePresentation.scalarOperator data)
        (SourcePresentation.multisetOperator data) P context x).2]
    exact multisetOperatorTruth data n arity Gamma hcal context _ x

theorem actualAllTermsFormulaTruth : SourcePresentationTargets.ActualAllTermsFormulaTruth := by
  intro data n arity Gamma hcal context P
  rw [SourcePresentation.allTermsFormula,allScalarTruth]
  apply forall_congr'
  intro x
  rw [generalImpTruth,embeddingTruth]
  have hc : FirstOrder.Language.Formula.Realize ((SourcePresentation.checkerFormula data.scalar).subst
      ![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))])
      (Sum.elim Empty.elim (fun _ : Fin 1 => x)) ↔
      OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x := by
    simp only [FirstOrder.Language.Formula.Realize]
    rw [BoundedFormula.realize_subst]
    have hv : (fun a : Fin 2 =>
        (![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))] a).realize
          (Sum.elim Empty.elim (fun _ : Fin 1 => x))) = ![context,x] := by
      funext i
      exact Fin.cases (numeralTruth context _)
        (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [hv]
    exact scalarCarrierTruth data n arity Gamma hcal context x
  rw [hc,predicateTruth,PositiveArithmeticTransformsProof.tagTermTruth]
  rfl

theorem actualInternalSourceSoundness : SourcePresentationTargets.ActualInternalSourceSoundness := by
  intro data n arity Gamma hcal symbols S table hclosed hproof x hx
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let body := SourcePresentation.sourceBody data context
  let P := standardLeastPredicate body
  have hall : ∀ z, OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context z → P (tagNumber false z) := by
    apply (actualAllTermsFormulaTruth data n arity Gamma hcal context P).mp
    apply InternalCalculusProof.actualInternalCalculusSoundness body P
      (InternalCalculusSupportProof.actualStandardLeastModel body) Empty []
      (SourcePresentation.allTermsFormula data context) hproof Empty.elim
    intro p hp
    cases hp
  let A : Set Nat := {z | Acc (fun successor source => encodedR n arity Gamma context source successor) z}
  let B : Set Nat := {z | Acc (fun successor source => OrdinaryArithmeticDirect.encodedDirect n arity Gamma context source successor) z}
  let Q := PositiveArithmeticLeastSetSupportProof.joinTags A B
  have hle : PositiveArithmeticLeastSet.leastSet
      (PositiveArithmeticTransforms.relabel (fun _ => (1 : Fin 2)) body) 0 ⊆ Q := by
    apply PositiveArithmeticLeastSetSupportProof.leastness
    intro z hz
    have hz' := (InternalCalculusSupportProof.closedBodyTruth body (fun y => y ∈ Q) z).mp hz
    have hval : (fun _ : Fin 1 => z) = ![z] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hval] at hz'
    obtain ⟨⟨odd,a⟩,he,hu⟩ := TaggedArithmeticOperatorsProof.tagPartition z
    subst z
    cases odd
    · apply (PositiveArithmeticLeastSetSupportProof.joinEven A B a).mpr
      refine Acc.intro a ?_
      intro y hy
      exact (PositiveArithmeticLeastSetSupportProof.joinEven A B y).mp
        (((actualClosedSourceOperator data n arity Gamma hcal context (fun z => z ∈ Q) a).1.mp hz').2 y hy)
    · apply (PositiveArithmeticLeastSetSupportProof.joinOdd A B a).mpr
      refine Acc.intro a ?_
      intro y hy
      exact (PositiveArithmeticLeastSetSupportProof.joinOdd A B y).mp
        (((actualClosedSourceOperator data n arity Gamma hcal context (fun z => z ∈ Q) a).2.mp hz').2 y hy)
  exact (PositiveArithmeticLeastSetSupportProof.joinEven A B x).mp (hle (hall x hx))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationProof
