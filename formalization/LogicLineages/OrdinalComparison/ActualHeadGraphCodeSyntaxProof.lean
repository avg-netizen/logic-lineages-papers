module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeConstantsProof
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
open ForwardTranslation Arithmetic ArithmeticCode FormulaConstruction

private theorem prefix_exact (a : ClosedPositive) (c δ : Nat) (t y : Expr) :
    finitePrefixCode (closedPositiveCode a) c δ (exprCode t) (exprCode y) =
      formulaCode (finitePrefix a c δ t y) := by
  have hc := exactGenuineConstants a c δ
  unfold finitePrefixCode finitePrefix
  rw [hc.2.2.2.1, hc.2.1, ← ArithmeticCode.Proof.exactFormulaConstructors.2.1]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' : actualOrdinalNorm (shiftedHead a δ) ≤ j := by
    exact of_decide_eq_true (List.mem_filter.mp hj).2
  rw [hc.2.2.2.2 j hj']
  rfl

private theorem tail_exact {Γ : List Ty} (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c δ : Nat) (t y : Expr) :
    tailCode Γ.length (closedPositiveCode a) c δ (UnitEliminationTreeCode.code q)
      (exprCode t) (exprCode y) = formulaCode (tail q a c δ t y) := by
  have hc := exactGenuineConstants a c δ
  have hu := UnitArithmeticFormulaCode.Proof.exactTreeExpansion (.ground::Γ) q
    (.variable 1 :: List.replicate Γ.length (.numeral 0)) (.variable 0)
  simp only [List.map_cons, List.map_replicate, exprCode] at hu
  unfold tailCode tail
  rw [hc.2.2.2.1, hc.2.2.1,
    ArithmeticCode.Proof.exactExpressionLift, ArithmeticCode.Proof.exactExpressionLift, hu]
  have hp := ArithmeticCode.Proof.exactFixedControl.2.2 δ (t.lift 2)
    (.add (.numeral (ActualUnaryRay.totalNorm a c 0)) (.variable 1))
  simp only [exprCode] at hp
  rw [hp]
  simp only [formulaCode, conjunctionCode, conjunction, List.foldr_cons, List.foldr_nil, exprCode]

theorem exactFormulaCompilation : Targets.ExactFormulaCompilation := by
  intro Γ q a c δ t y
  unfold graphCode graph
  rw [prefix_exact, tail_exact]
  rfl
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
