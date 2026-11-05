module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsForestBridge

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
open NormalForm LinearRows
open LogicLineages.ModelsAlgebra.Forests
open CotreePresburgerLinear

@[simp] theorem forest_weight (i : Nat) (ν : Nat → Nat) (a : Atom) :
    CotreePresburgerNormalize.weight (forestAtom1 i ν a) = weight i a := by
  cases a <;> rfl

theorem forest_modulus (i : Nat) (ν : Nat → Nat) (p : Formula) :
    CotreePresburgerNormalize.coefficientModulus (forestFormula1 i ν p) =
      coefficientModulus i p := by
  simp [CotreePresburgerNormalize.coefficientModulus, coefficientModulus,
    forestFormula1, liftFormula_atoms, List.map_map, Function.comp_def]

theorem forest_adjust_atom (i M : Nat) (ν : Nat → Nat) (a : Atom) :
    forestUnitAtom ν (adjustAtom i M a) =
      CotreePresburgerNormalize.adjustAtom M (forestAtom1 i ν a) := by
  cases a with
  | nonnegative r =>
      by_cases h : leading i r = 0 <;>
        simp [adjustAtom, forestAtom1, forestUnitAtom,
          CotreePresburgerNormalize.adjustAtom, h, nonzeroSign,
          CotreePresburgerNormalize.nonzeroSign]
  | divisible m r =>
      by_cases h : leading i r = 0 <;>
        simp [adjustAtom, forestAtom1, forestUnitAtom,
          CotreePresburgerNormalize.adjustAtom, h, nonzeroSign,
          CotreePresburgerNormalize.nonzeroSign]

theorem forest_adjust (i M : Nat) (ν : Nat → Nat) (p : Formula) :
    forestUnit ν (adjust i M p) =
      CotreePresburgerNormalize.adjust M (forestFormula1 i ν p) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact congrArg CotreePresburgerUnit.Boolean.atom (forest_adjust_atom i M ν a)
  | negative p ih => exact congrArg CotreePresburgerUnit.Boolean.neg ih
  | conjunction p q ihp ihq => exact congrArg₂ CotreePresburgerUnit.Boolean.conj ihp ihq
  | disjunction p q ihp ihq => exact congrArg₂ CotreePresburgerUnit.Boolean.disj ihp ihq

theorem forest_normalize (i : Nat) (ν : Nat → Nat) (p : Formula) :
    forestUnit ν (normalize i p) =
      CotreePresburgerNormalize.normalize (forestFormula1 i ν p) := by
  unfold LinearRows.normalize CotreePresburgerNormalize.normalize
  rw [forest_modulus]
  change CotreePresburgerUnit.Boolean.conj
      (.atom (.dvd (coefficientModulus i p - 1) .pos (forestRow0 ν (rowConst 0))))
      (forestUnit ν (adjust i (coefficientModulus i p) p)) =
    CotreePresburgerUnit.Boolean.conj
      (.atom (.dvd (coefficientModulus i p - 1) .pos (Affine.const 0)))
      (CotreePresburgerNormalize.adjust (coefficientModulus i p) (forestFormula1 i ν p))
  rw [forestRow0_const, forest_adjust]

@[simp] theorem forest_unit_period_atom (ν : Nat → Nat) (a : UnitAtom) :
    CotreePresburgerUnit.UnitAtom.period (forestUnitAtom ν a) = a.period := by
  cases a <;> rfl

theorem forest_period (ν : Nat → Nat) (u : UnitFormula) :
    CotreePresburgerUnit.period (forestUnit ν u) = period u := by
  simp [CotreePresburgerUnit.period, period, forestUnit, boolean_map_atoms,
    List.map_map, Function.comp_def]

theorem forest_cutoffs_atom (ν : Nat → Nat) (a : UnitAtom) :
    (a.cutoffs.map (forestRow0 ν)) =
      CotreePresburgerUnit.UnitAtom.cutoffs (forestUnitAtom ν a) := by
  cases a with
  | nonnegative s r =>
      cases s <;> simp [UnitAtom.cutoffs, forestUnitAtom, CotreePresburgerUnit.UnitAtom.cutoffs]
  | divisible m s r =>
      simp [UnitAtom.cutoffs, forestUnitAtom, CotreePresburgerUnit.UnitAtom.cutoffs]

theorem forest_cutoffs (ν : Nat → Nat) (u : UnitFormula) :
    (cutoffs u).map (forestRow0 ν) = CotreePresburgerUnit.cutoffs (forestUnit ν u) := by
  simp [cutoffs, CotreePresburgerUnit.cutoffs, forestUnit, boolean_map_atoms,
    List.map_flatMap, List.flatMap_map, Function.comp_def, forest_cutoffs_atom]

theorem forest_instantiate_atom (ν : Nat → Nat) (a : UnitAtom) (b : Row) :
    forestAtom0 ν (a.instantiate b) =
      CotreePresburgerUnit.UnitAtom.subst (forestRow0 ν b) (forestUnitAtom ν a) := by
  cases a <;> simp [UnitAtom.instantiate, forestAtom0, forestUnitAtom,
    CotreePresburgerUnit.UnitAtom.subst]

theorem forest_instantiate (ν : Nat → Nat) (u : UnitFormula) (b : Row) :
    forestFormula0 ν (instantiate u b) =
      CotreePresburgerUnit.instantiate (forestUnit ν u) (forestRow0 ν b) := by
  induction u with
  | bot => rfl
  | top => rfl
  | atom a => exact congrArg CotreePresburgerUnit.Boolean.atom (forest_instantiate_atom ν a b)
  | neg p ih => exact congrArg CotreePresburgerUnit.Boolean.neg ih
  | conj p q ihp ihq => exact congrArg₂ CotreePresburgerUnit.Boolean.conj ihp ihq
  | disj p q ihp ihq => exact congrArg₂ CotreePresburgerUnit.Boolean.disj ihp ihq

theorem forest_guarded (ν : Nat → Nat) (u : UnitFormula) :
    forestUnit ν (guarded u) = CotreePresburgerUnit.guarded (forestUnit ν u) := by
  change CotreePresburgerUnit.Boolean.conj
      (.atom (.nonneg .pos (forestRow0 ν (rowConst 0)))) (forestUnit ν u) = _
  rw [forestRow0_const]
  rfl

theorem forest_any (ν : Nat → Nat) (ps : List Formula) :
    forestFormula0 ν (BoundedRows.any ps) =
      CotreePresburgerUnit.Boolean.disjoin (ps.map (forestFormula0 ν)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      exact congrArg (CotreePresburgerUnit.Boolean.disj (forestFormula0 ν p)) ih

theorem forest_unit_eliminate (ν : Nat → Nat) (u : UnitFormula) :
    forestFormula0 ν (unitEliminate u) = CotreePresburgerUnit.eliminate (forestUnit ν u) := by
  unfold unitEliminate CotreePresburgerUnit.eliminate
  rw [forest_any, ← forest_cutoffs, forest_period]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    forest_instantiate, forest_guarded, forestRow0_add, forestRow0_const]

theorem forest_eliminate (i : Nat) (ν : Nat → Nat) (p : Formula) :
    forestFormula0 ν (eliminate i p) =
      CotreePresburgerNormalize.eliminate (forestFormula1 i ν p) := by
  simp only [eliminate, CotreePresburgerNormalize.eliminate,
    forest_unit_eliminate, forest_normalize]

theorem actualNormalization : LinearRowsTargets.ActualNormalization := by
  intro i p hp ν
  calc
    (∃ n : Nat, p.eval (Function.update ν i n)) ↔
        ∃ n : Nat, CotreePresburgerUnit.evalQF (forestFormula1 i ν p)
          (Fin.snoc emptyVal (n : Int)) = true :=
      exists_congr (fun n => (forestFormula1_eval i ν p hp n).symm)
    _ ↔ ∃ n : Nat, CotreePresburgerUnit.evalUnit
        (CotreePresburgerNormalize.normalize (forestFormula1 i ν p)) emptyVal (n : Int) = true :=
      CotreePresburgerNormalize.Proof.normalizationExact 0 (forestFormula1 i ν p) emptyVal
    _ ↔ ∃ n : Nat, unitEval (normalize i p) ν (n : Int) := by
      rw [← forest_normalize]
      exact exists_congr (fun n => forestUnit_eval ν (normalize i p) (n : Int))

theorem actualUnitElimination : LinearRowsTargets.ActualUnitElimination := by
  intro u ν
  calc
    (unitEliminate u).eval ν ↔
        CotreePresburgerUnit.evalQF (forestFormula0 ν (unitEliminate u)) emptyVal = true :=
      (forestFormula0_eval ν (unitEliminate u)).symm
    _ ↔ CotreePresburgerUnit.evalQF
        (CotreePresburgerUnit.eliminate (forestUnit ν u)) emptyVal = true := by
      rw [forest_unit_eliminate]
    _ ↔ ∃ n : Nat, CotreePresburgerUnit.evalUnit (forestUnit ν u) emptyVal (n : Int) = true :=
      CotreePresburgerUnit.Proof.unitEliminationExact 0 (forestUnit ν u) emptyVal
    _ ↔ ∃ n : Nat, unitEval u ν (n : Int) :=
      exists_congr (fun n => forestUnit_eval ν u (n : Int))

theorem actualLinearElimination : LinearRowsTargets.ActualLinearElimination := by
  intro i p hp ν
  calc
    (eliminate i p).eval ν ↔
        CotreePresburgerUnit.evalQF (forestFormula0 ν (eliminate i p)) emptyVal = true :=
      (forestFormula0_eval ν (eliminate i p)).symm
    _ ↔ CotreePresburgerUnit.evalQF
        (CotreePresburgerNormalize.eliminate (forestFormula1 i ν p)) emptyVal = true := by
      rw [forest_eliminate]
    _ ↔ ∃ n : Nat, CotreePresburgerUnit.evalQF (forestFormula1 i ν p)
        (Fin.snoc emptyVal (n : Int)) = true :=
      CotreePresburgerNormalize.Proof.eliminationExact 0 (forestFormula1 i ν p) emptyVal
    _ ↔ ∃ n : Nat, p.eval (Function.update ν i n) :=
      exists_congr (fun n => forestFormula1_eval i ν p hp n)

theorem actualGuardedAtomElimination : LinearRowsTargets.ActualGuardedAtomElimination := by
  intro i a h ν
  rw [actualLinearElimination i (guardedAtom a) h ν]
  apply exists_congr
  intro n
  exact and_congr
    (NormalFormSemanticProof.exactOriginalRowDomains a.row (Function.update ν i n)) Iff.rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
