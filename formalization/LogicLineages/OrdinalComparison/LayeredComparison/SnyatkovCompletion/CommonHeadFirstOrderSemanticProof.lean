module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesLiteralProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProof
open CommonHeadFirstOrder CommonLayerSyntax

theorem actualSourceTranslation : CommonHeadFirstOrderTargets.ActualSourceTranslation := by
  intro p
  induction p with
  | compare heads E F d =>
    intro hc ν
    rw [translate, BaseBooleanSourceProof.exactTranslation]
    have h := (CommonHeadExactVariablesProof.actualSourceClause heads hc E F d).1 ν
    rw [CommonHeadExactVariablesProof.literalCodeCalibration,
      (CommonHeadExactVariablesCalibration.literalBaseFormulaCode _).1 ν] at h
    exact h
  | negative p ih => intro hp ν; exact not_congr (ih hp ν)
  | conjunction p q ihp ihq => intro hp ν; exact and_congr (ihp hp.1 ν) (ihq hp.2 ν)
  | existsNat i p ih =>
    intro hp ν
    exact exists_congr (fun n => ih hp (Function.update ν i n))
  | existsPositive i p ih =>
    intro hp ν
    change (∃ n : Nat, 0 < Function.update ν i n i ∧ (translate p).eval (Function.update ν i n)) ↔ _
    simp only [Function.update_self]
    exact exists_congr (fun n => and_congr Iff.rfl (ih hp (Function.update ν i n)))

theorem exactFreeVariables : CommonHeadFirstOrderTargets.ExactFreeVariables := by
  intro p
  induction p with
  | compare heads E F d =>
    intro i
    rw [translate, (BaseBooleanSourceProof.exactSourceData _).2,
      (CommonHeadExactVariablesProof.rawTruthAndExactSupport _ _ _ _).2 i]
    have hlen : (headCodes heads).length = heads.length := List.length_map _
    unfold CommonLayerComparison.codedVariables
    rw [hlen, CommonLayerSyntax.Proof.commonRoundtrip heads.length E,
      CommonLayerSyntax.Proof.commonRoundtrip heads.length F]
    rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    intro i
    simp only [translate, SourceFormula.variables, Formula.variables, List.mem_append, ihp, ihq]
  | existsNat i p ih =>
    intro j
    simp only [translate, SourceFormula.variables, Formula.variables, List.mem_filter, ih]
  | existsPositive i p ih =>
    intro j
    simp only [translate, SourceFormula.variables, BaseTerm.variables, Formula.variables,
      List.nil_append, List.mem_filter, List.mem_append, List.mem_singleton, ih,
      bne_iff_ne, ne_eq]
    tauto

theorem exactUniversalDomains : CommonHeadFirstOrderTargets.ExactUniversalDomains := by
  classical
  intro p hp i ν
  have hn : (forallNat i p).certified := hp
  have hpos : (forallPositive i p).certified := hp
  rw [actualSourceTranslation _ hn, actualSourceTranslation _ hpos]
  simp only [forallNat, forallPositive, Formula.eval, not_exists, not_not, not_and]
  trivial

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProof
