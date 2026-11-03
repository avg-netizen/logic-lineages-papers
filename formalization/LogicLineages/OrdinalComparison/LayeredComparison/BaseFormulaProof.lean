module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
public import LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntimeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula.Proof
open CommonLayerSyntax

private theorem base_roundtrip (E:BaseTerm):BaseTerm.decode E.encode=E:=
  CommonLayerSyntax.Proof.baseRoundtrip E

private theorem viewTruth (p:Formula) (ν:Nat→Nat):
    p.guardView.eval (termValuation ν)↔p.eval ν:=by
  induction p with
  | truth=>rfl
  | falsity=>rfl
  | equal E F=>
    simp only [Formula.guardView,CommonHeadLargeGuards.Formula.eval,termValuation,
      base_roundtrip,Formula.eval]
  | less E F=>
    simp only [Formula.guardView,CommonHeadLargeGuards.Formula.eval,termValuation,
      base_roundtrip,Formula.eval]
  | negative p ih=>exact not_congr ih
  | conjunction p q ihp ihq=>exact and_congr ihp ihq
  | disjunction p q ihp ihq=>exact or_congr ihp ihq

private theorem viewVariables (p:Formula):
    p.guardView.variables.flatMap (fun t=>(BaseTerm.decode t).variables)=p.variables:=by
  induction p with
  | truth=>rfl
  | falsity=>rfl
  | equal E F=>simp [Formula.guardView,CommonHeadLargeGuards.Formula.variables,
      Formula.variables,base_roundtrip]
  | less E F=>simp [Formula.guardView,CommonHeadLargeGuards.Formula.variables,
      Formula.variables,base_roundtrip]
  | negative p ih=>exact ih
  | conjunction p q ihp ihq=>
    simp only [Formula.guardView,CommonHeadLargeGuards.Formula.variables,
      List.flatMap_append,ihp,ihq,Formula.variables]
  | disjunction p q ihp ihq=>
    simp only [Formula.guardView,CommonHeadLargeGuards.Formula.variables,
      List.flatMap_append,ihp,ihq,Formula.variables]

theorem literalBaseFormulaCode:Targets.LiteralBaseFormulaCode:=by
  intro p
  refine ⟨?_,?_⟩
  · intro ν
    unfold evaluate Formula.encode GuardCodeRuntime.evaluate
    rw [(GuardCodeRuntime.Proof.literalEncoding p.guardView).1]
    simp only [List.headD_cons]
    exact ((GuardCodeRuntime.Proof.literalEncoding p.guardView).2.2 _).trans (viewTruth p ν)
  · unfold rawVariables Formula.encode
    rw [(GuardCodeRuntime.Proof.literalEncoding p.guardView).2.1]
    exact viewVariables p
end LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula.Proof
