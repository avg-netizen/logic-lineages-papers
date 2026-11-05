module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsAlgebraProof
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
open NormalForm LinearRows
open LogicLineages.ModelsAlgebra.Forests
open CotreePresburgerLinear

/-- This valuation has no independent residual coordinates. -/
def emptyVal : Fin 0 → Int := Fin.elim0

/-- Residual rows are interpreted at one fixed original valuation. -/
def forestRow0 (ν : Nat → Nat) (r : Row) : Affine 0 :=
  Affine.const (rowValue r ν)

def forestRow1 (i : Nat) (ν : Nat → Nat) (r : Row) : Affine 1 :=
  ⟨rowValue (remainder i r) ν, fun _ => leading i r⟩

theorem affine0_ext (a b : Affine 0) (h : a.constant = b.constant) : a = b := by
  rcases a with ⟨ac, af⟩
  rcases b with ⟨bc, bf⟩
  change ac = bc at h
  subst bc
  have hf : af = bf := funext (fun k => Fin.elim0 k)
  cases hf
  rfl

@[simp] theorem forestRow0_const (ν : Nat → Nat) (z : Int) :
    forestRow0 ν (rowConst z) = Affine.const z := by
  apply affine0_ext
  exact rowConst_value z ν

@[simp] theorem forestRow0_add (ν : Nat → Nat) (r s : Row) :
    forestRow0 ν (rowAdd r s) = Affine.add (forestRow0 ν r) (forestRow0 ν s) := by
  apply affine0_ext
  exact rowAdd_value r s ν

@[simp] theorem forestRow0_scale (ν : Nat → Nat) (z : Int) (r : Row) :
    forestRow0 ν (rowScale z r) = Affine.scale z (forestRow0 ν r) := by
  apply affine0_ext
  exact rowScale_value z r ν

@[simp] theorem forestRow0_eval (ν : Nat → Nat) (r : Row) :
    (forestRow0 ν r).eval emptyVal = rowValue r ν := by
  simp [forestRow0]

@[simp] theorem forestRow1_last (i : Nat) (ν : Nat → Nat) (r : Row) :
    Affine.lastCoeff (forestRow1 i ν r) = leading i r := rfl

@[simp] theorem forestRow1_drop (i : Nat) (ν : Nat → Nat) (r : Row) :
    Affine.dropLast (forestRow1 i ν r) = forestRow0 ν (remainder i r) := by
  apply affine0_ext
  rfl

theorem forestRow1_eval (i : Nat) (ν : Nat → Nat) (r : Row) (x : Int) :
    (forestRow1 i ν r).eval (Fin.snoc emptyVal x) =
      rowValue (remainder i r) ν + leading i r * x := by
  simpa only [forestRow1_drop, forestRow0_eval, forestRow1_last] using
    CotreePresburgerLinear.Proof.lastVariableSplitExact 0 (forestRow1 i ν r) emptyVal x

def liftFormula {A : Type} (f : Atom → A) : Formula → Boolean A
  | .truth => .top
  | .falsity => .bot
  | .atom a => .atom (f a)
  | .negative p => .neg (liftFormula f p)
  | .conjunction p q => .conj (liftFormula f p) (liftFormula f q)
  | .disjunction p q => .disj (liftFormula f p) (liftFormula f q)

theorem liftFormula_atoms {A : Type} (f : Atom → A) (p : Formula) :
    (liftFormula f p).atoms = (atoms p).map f := by
  induction p <;>
    simp [liftFormula, atoms, CotreePresburgerUnit.Boolean.atoms, List.map_append, *]

theorem boolean_map_atoms {A B : Type} (f : A → B) (u : Boolean A) :
    (u.map f).atoms = u.atoms.map f := by
  induction u <;>
    simp [CotreePresburgerUnit.Boolean.map, CotreePresburgerUnit.Boolean.atoms,
      List.map_append, *]

def forestAtom0 (ν : Nat → Nat) : Atom → CotreePresburgerUnit.Atom 0
  | .nonnegative r => .nonneg (forestRow0 ν r)
  | .divisible m r => .dvd m (forestRow0 ν r)

def forestFormula0 (ν : Nat → Nat) (p : Formula) : CotreePresburgerUnit.QF 0 :=
  liftFormula (forestAtom0 ν) p

def forestAtom1 (i : Nat) (ν : Nat → Nat) : Atom → CotreePresburgerUnit.Atom 1
  | .nonnegative r => .nonneg (forestRow1 i ν r)
  | .divisible m r => .dvd m (forestRow1 i ν r)

def forestFormula1 (i : Nat) (ν : Nat → Nat) (p : Formula) :
    CotreePresburgerUnit.QF 1 := liftFormula (forestAtom1 i ν) p

def forestUnitAtom (ν : Nat → Nat) : UnitAtom → CotreePresburgerUnit.UnitAtom 0
  | .nonnegative s r => .nonneg s (forestRow0 ν r)
  | .divisible m s r => .dvd m s (forestRow0 ν r)

def forestUnit (ν : Nat → Nat) (u : UnitFormula) : CotreePresburgerUnit.UnitFormula 0 :=
  u.map (forestUnitAtom ν)

theorem forestAtom0_eval (ν : Nat → Nat) (a : Atom) :
    CotreePresburgerUnit.Atom.eval emptyVal (forestAtom0 ν a) = true ↔ a.eval ν := by
  cases a <;> simp [forestAtom0, CotreePresburgerUnit.Atom.eval, Atom.eval]

theorem forestFormula0_eval (ν : Nat → Nat) (p : Formula) :
    CotreePresburgerUnit.evalQF (forestFormula0 ν p) emptyVal = true ↔ p.eval ν := by
  induction p with
  | truth => simp [forestFormula0, liftFormula, CotreePresburgerUnit.evalQF,
      CotreePresburgerUnit.Boolean.eval, Formula.eval]
  | falsity => simp [forestFormula0, liftFormula, CotreePresburgerUnit.evalQF,
      CotreePresburgerUnit.Boolean.eval, Formula.eval]
  | atom a => exact forestAtom0_eval ν a
  | negative p ih =>
      simpa [forestFormula0, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using not_congr ih
  | conjunction p q ihp ihq =>
      simpa [forestFormula0, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using and_congr ihp ihq
  | disjunction p q ihp ihq =>
      simpa [forestFormula0, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using or_congr ihp ihq

theorem forestAtom1_eval (i : Nat) (ν : Nat → Nat) (a : Atom)
    (ha : rowLinear i a.row = true) (n : Nat) :
    CotreePresburgerUnit.Atom.eval (Fin.snoc emptyVal (n : Int)) (forestAtom1 i ν a) =
      true ↔ a.eval (Function.update ν i n) := by
  have hs := actualLinearRowSplit i a.row ha ν n
  cases a <;>
    simp only [Atom.row] at hs <;>
    simp only [forestAtom1, CotreePresburgerUnit.Atom.eval, Atom.eval,
      forestRow1_eval, decide_eq_true_eq] <;> rw [hs]

theorem forestFormula1_eval (i : Nat) (ν : Nat → Nat) (p : Formula) :
    isLinear i p = true → ∀ n : Nat,
      CotreePresburgerUnit.evalQF (forestFormula1 i ν p)
        (Fin.snoc emptyVal (n : Int)) = true ↔ p.eval (Function.update ν i n) := by
  induction p with
  | truth => intro _ n; simp [forestFormula1, liftFormula, CotreePresburgerUnit.evalQF,
      CotreePresburgerUnit.Boolean.eval, Formula.eval]
  | falsity => intro _ n; simp [forestFormula1, liftFormula, CotreePresburgerUnit.evalQF,
      CotreePresburgerUnit.Boolean.eval, Formula.eval]
  | atom a =>
      intro ha n
      exact forestAtom1_eval i ν a (by simpa [isLinear, atoms] using ha) n
  | negative p ih =>
      intro hp n
      have hp' : isLinear i p = true := hp
      simpa [forestFormula1, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using not_congr (ih hp' n)
  | conjunction p q ihp ihq =>
      intro hpq n
      have h : isLinear i p = true ∧ isLinear i q = true := by
        simpa [isLinear, atoms, List.all_append] using hpq
      simpa [forestFormula1, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using
        and_congr (ihp h.1 n) (ihq h.2 n)
  | disjunction p q ihp ihq =>
      intro hpq n
      have h : isLinear i p = true ∧ isLinear i q = true := by
        simpa [isLinear, atoms, List.all_append] using hpq
      simpa [forestFormula1, liftFormula, CotreePresburgerUnit.evalQF,
        CotreePresburgerUnit.Boolean.eval, Formula.eval] using
        or_congr (ihp h.1 n) (ihq h.2 n)

theorem forestUnitAtom_eval (ν : Nat → Nat) (a : UnitAtom) (x : Int) :
    CotreePresburgerUnit.UnitAtom.eval emptyVal x (forestUnitAtom ν a) = true ↔
      a.eval ν x := by
  cases a <;> simp [forestUnitAtom, CotreePresburgerUnit.UnitAtom.eval, UnitAtom.eval]

theorem forestUnit_eval (ν : Nat → Nat) (u : UnitFormula) (x : Int) :
    CotreePresburgerUnit.evalUnit (forestUnit ν u) emptyVal x = true ↔ unitEval u ν x := by
  induction u with
  | bot => simp [forestUnit, CotreePresburgerUnit.Boolean.map,
      CotreePresburgerUnit.evalUnit, CotreePresburgerUnit.Boolean.eval, unitEval]
  | top => simp [forestUnit, CotreePresburgerUnit.Boolean.map,
      CotreePresburgerUnit.evalUnit, CotreePresburgerUnit.Boolean.eval, unitEval]
  | atom a => exact forestUnitAtom_eval ν a x
  | neg p ih =>
      simpa [forestUnit, CotreePresburgerUnit.Boolean.map,
        CotreePresburgerUnit.evalUnit, CotreePresburgerUnit.Boolean.eval, unitEval] using
        not_congr ih
  | conj p q ihp ihq =>
      simpa [forestUnit, CotreePresburgerUnit.Boolean.map,
        CotreePresburgerUnit.evalUnit, CotreePresburgerUnit.Boolean.eval, unitEval] using
        and_congr ihp ihq
  | disj p q ihp ihq =>
      simpa [forestUnit, CotreePresburgerUnit.Boolean.map,
        CotreePresburgerUnit.evalUnit, CotreePresburgerUnit.Boolean.eval, unitEval] using
        or_congr ihp ihq

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
