module
public import LogicLineages.OrdinalComparison.UnitHeadCodeTargets
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadCode.Proof
open ForwardTranslation

theorem unit_exact {Γ} (q : OrdinalExpression Γ) :
    unitCode (OrdinalSyntax.typedCode q) = OrdinalSyntax.typedCode (UnitHeadEvaluation.unitSyntax q) := by
  unfold unitCode OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | zero | one | omega => rfl
  | var c =>
    have hm : (8*OrdinalSyntax.componentCode c+3)%8=3 := by omega
    simp [OrdinalSyntax.termFold,unitLeaf,hm,UnitHeadEvaluation.unitSyntax,OrdinalSyntax.code]
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [OrdinalSyntax.termFold,UnitHeadEvaluation.unitSyntax,OrdinalSyntax.code,unitBranch]
    rw [iha,ihb]

theorem exactRawUnitExtraction : Targets.ExactRawUnitExtraction := by
  intro Γ q
  refine ⟨unit_exact q,?_⟩
  rw [positiveCode,unit_exact]
  exact congrArg Prod.fst (OrdinalSyntax.ordinalSyntaxExtractionCorrect Γ (UnitHeadEvaluation.unitSyntax q))

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  have hl : Primrec unitLeaf := Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 8)) (Primrec.const 3))
    (Primrec.const 1) Primrec.id
  have hb : Primrec (fun p : Nat × Nat × Nat => unitBranch p.1 p.2.1 p.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 8)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))) Primrec.fst
  have hu : Primrec unitCode := OrdinalSyntax.ordinalSyntaxFoldPrimitiveRecursive _ _ _ hl hb
  have hp : Primrec positiveCode := Primrec.fst.comp
    (OrdinalSyntax.ordinalSyntaxExtractionPrimitiveRecursive.comp hu)
  have hn := UnitHeadEvaluation.Proof.exactNumericBridge.1
  have hf := UnitHeadEvaluation.Proof.exactNumericBridge.2.1
  have hv := UnitHeadEvaluation.Proof.exactNumericBridge.2.2.1
  have hc : Primrec classify := Primrec.option_map hp ((hn.pair (hf.pair hv)).comp Primrec.snd).to₂
  exact ⟨hu,hp,hc⟩

theorem actualPositiveClassification : Targets.ActualPositiveClassification := by
  intro Γ i q hg hi
  obtain ⟨a,ha,hev,hval⟩ := UnitHeadEvaluation.Proof.generatedPositiveEvaluation Γ i q hg hi
  have hp : positiveCode (OrdinalSyntax.typedCode q) = some (closedPositiveCode a) := by
    rw [(exactRawUnitExtraction Γ q).2,ha]
    rfl
  have hc := UnitHeadEvaluation.Proof.exactNumericBridge.2.2.2 a
  let finite := UnitHeadEvaluation.finiteCode (closedPositiveCode a)
  let value := UnitHeadEvaluation.finiteValueCode (closedPositiveCode a)
  have hfinite : finite = true ↔ _ := hc.2.1
  refine ⟨a,finite,value,hp,?_,hval,?_,?_,?_⟩
  · simp [classify,hp,hc.1,finite,value]
  · rw [← hval]
    exact hfinite
  · constructor
    · intro hf
      apply le_of_not_gt
      intro hlt
      have ht := hfinite.mpr (hval.symm ▸ hlt)
      rw [hf] at ht
      contradiction
    · intro hnon
      cases hf : finite with
      | false => rfl
      | true => exact False.elim ((not_lt_of_ge hnon) (hval ▸ (hfinite.mp hf)))
  · intro hf
    exact (hc.2.2 hf).trans hval
end LogicLineages.OrdinalComparison.Source.UnitHeadCode.Proof
