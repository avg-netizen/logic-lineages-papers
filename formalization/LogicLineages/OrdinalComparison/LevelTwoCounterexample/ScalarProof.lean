module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarTargets
import LogicLineages.OrdinalComparison.WWSourceClassesFullProof
import LogicLineages.OrdinalComparison.WWScalarTranslationProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSemanticStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarProof
open Source Source.ForwardTranslation Source.SourceClasses PolynomialGraphCompletion

private theorem head_repr (c : ClosedPositive) : (scalarHeadNote c).1.repr = fixedHead c := by
  rw [scalarHeadNote, naturalProductDenotation]
  simp [fixedHead, ONote.repr]

theorem exactOriginalNames : ScalarTargets.ExactOriginalNames := by
  intro ι index s
  induction s with
  | one => rfl
  | var x => rfl
  | add a b iha ihb => simp only [scalarExpr, Expr.variables, scalarNames, List.map_append, iha, ihb]
  | shift c a ih => exact ih

theorem exactScalarValue : ScalarTargets.ExactScalarValue := by
  intro ι index s ν
  induction s with
  | one => rfl
  | var x => rfl
  | add a b iha ihb => simp only [scalarExpr, Expr.value, Scalar.value, iha, ihb]
  | shift c a ih =>
    simp only [scalarExpr, Expr.value, headValue, rawNoteDecodeEncode (scalarHeadNote c).1, head_repr, Scalar.value, ih]

private theorem valid_head (c : ClosedPositive)
    (h : Order.IsSuccLimit (fixedHead c) ∧ fixedHead c < Ordinal.omega0 ^ Ordinal.omega0) :
    ValidHead (rawNoteEncode (scalarHeadNote c).1) := by
  simp only [ValidHead, rawNoteDecodeEncode (scalarHeadNote c).1]
  exact ⟨(scalarHeadNote c).2, by simpa only [head_repr] using h⟩

theorem validPolynomialExpression : ScalarTargets.ValidPolynomialExpression := by
  intro ι index s h
  induction s with
  | one => intro code hc; simp [scalarExpr, Expr.heads] at hc
  | var x => intro code hc; simp [scalarExpr, Expr.heads] at hc
  | add a b iha ihb =>
    have ha : PolynomialScalar a := fun c hc => h c (List.mem_append_left _ hc)
    have hb : PolynomialScalar b := fun c hc => h c (List.mem_append_right _ hc)
    intro code hc
    rcases List.mem_append.mp hc with hc | hc
    · exact iha ha code hc
    · exact ihb hb code hc
  | shift c a ih =>
    have ha : PolynomialScalar a := fun d hd => h d (List.mem_cons_of_mem c hd)
    intro code hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih ha code hc
    · have he : code = rawNoteEncode (scalarHeadNote c).1 := List.mem_singleton.mp hc
      subst code
      exact valid_head c (h c List.mem_cons_self)

theorem actualLevelTwoScalar : ScalarTargets.ActualLevelTwoScalar := by
  intro Γ hΓ τ p t ht index
  obtain ⟨v, hv, s, hs, hh⟩ := actualSourceClasses.2 Γ hΓ τ p t ht
  refine ⟨v, s, hv, hs, validPolynomialExpression _ index s hh, ?_⟩
  intro ν
  rw [exactScalarValue]
  exact scalarTranslationSound Γ (v 0) s hs (fun c => ν (index c))

theorem sourceScalarGraph : ScalarTargets.SourceScalarGraph := by
  intro ι index s hs resultName ν
  rw [ExpressionSemanticStatementChecks.correlated_existential_graph
    (scalarExpr index s) (validPolynomialExpression _ index s hs) resultName ν,
    exactScalarValue]
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarProof
