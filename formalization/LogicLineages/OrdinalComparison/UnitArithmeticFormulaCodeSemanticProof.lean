module
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeTargets
public import LogicLineages.OrdinalComparison.ActualArithmeticCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
open Arithmetic ArithmeticCode

private theorem mod_tag (a tag : Nat) (h : tag<4) : (4*a+tag)%4=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<4) : (4*a+tag)/4=a := by omega

private theorem leaf_eq (p : Nat) (xs : List Nat) (r : Nat) :
    unitFormulaCode (UnitEliminationTreeCode.leafCode p) xs r = leafFormula p xs r := by
  rw [unitFormulaCode.eq_def]
  simp [UnitEliminationTreeCode.leafCode]

private theorem free_eq (p q : Nat) (xs : List Nat) (r : Nat) :
    unitFormulaCode (UnitEliminationTreeCode.freeCode p q) xs r =
      freeFormula p r (unitFormulaCode q (shifted 1 (deleted (freeData p).1.length xs))
        (positiveVariable 0)) := by
  rw [unitFormulaCode.eq_def]
  simp [UnitEliminationTreeCode.freeCode,mod_tag _ 1 (by decide),div_tag _ 1 (by decide)]

private theorem active_eq (p q s : Nat) (xs : List Nat) (r : Nat) :
    unitFormulaCode (UnitEliminationTreeCode.activeCode p q s) xs r =
      activeFormula p r
        (unitFormulaCode q (shifted 2 (deleted (activeData p).1.length xs)) (positiveVariable 1))
        (unitFormulaCode s (shifted 2 (deleted (activeData p).1.length xs)) (positiveVariable 0)) := by
  rw [unitFormulaCode.eq_def]
  simp [UnitEliminationTreeCode.activeCode,mod_tag _ 2 (by decide),div_tag _ 2 (by decide)]

private theorem lift_exact (k : Nat) (a : Expr) :
    liftCode k (exprCode a) = exprCode (a.lift k) :=
  ArithmeticCode.Proof.exactExpressionLift k a

private theorem shifted_map (k : Nat) (xs : List Expr) :
    shifted k (xs.map exprCode) = (xs.map (Expr.lift k)).map exprCode := by
  simp only [shifted, List.map_map, Function.comp_def, lift_exact]

private theorem deleted_map (i : Nat) (xs : List Expr) :
    deleted i (xs.map exprCode) = (xs.take i ++ xs.drop (i+1)).map exprCode := by
  simp [deleted]

theorem exactTreeExpansion : Targets.ExactTreeExpansion := by
  intro Γ q
  induction q with
  | leaf b =>
    intro xs r
    rw [UnitEliminationTreeCode.code, leaf_eq]
    simp [leafFormula, leafData, UnitGroundBlockCode.blockCode, shifted_map,
      positiveVariable, unitFormula, formulaCode, conjunctionCode, conjunction,
      exprCode, lift_exact]
  | free left right σ d q ih =>
    intro xs r
    rw [UnitEliminationTreeCode.code, free_eq]
    simp only [freeData, UnitEliminationTreeCode.freeMetadata, Encodable.encodek,
      Option.getD_some, List.length_map, deleted_map, shifted_map]
    change freeFormula _ (exprCode r)
      (unitFormulaCode (UnitEliminationTreeCode.code q)
        (((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 1)).map exprCode)
        (exprCode (.add (.variable 0) (.numeral 1)))) = _
    rw [ih]
    simp [freeFormula, freeData, UnitEliminationTreeCode.freeMetadata,
      positiveVariable, unitFormula, formulaCode, exprCode, lift_exact]
  | active left right σ p d d' c q s ihq ihs =>
    intro xs r
    rw [UnitEliminationTreeCode.code, active_eq]
    simp only [activeData, UnitEliminationTreeCode.activeMetadata, Encodable.encodek,
      Option.getD_some, List.length_map, deleted_map, shifted_map]
    change activeFormula _ (exprCode r)
      (unitFormulaCode (UnitEliminationTreeCode.code q)
        (((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 2)).map exprCode)
        (exprCode (.add (.variable 1) (.numeral 1))))
      (unitFormulaCode (UnitEliminationTreeCode.code s)
        (((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 2)).map exprCode)
        (exprCode (.add (.variable 0) (.numeral 1)))) = _
    rw [ihq, ihs]
    simp [activeFormula, activeData, UnitEliminationTreeCode.activeMetadata,
      positiveVariable, unitFormula, formulaCode, conjunctionCode, conjunction,
      exprCode, lift_exact]
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
