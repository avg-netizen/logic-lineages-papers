module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnitStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize
open CotreePresburgerLinear CotreePresburgerUnit

/-- The actual coefficient of the newest variable in an arbitrary affine atom. -/
def leading {n : Nat} : Atom (n + 1) → Int
  | .nonneg t | .dvd _ t => Affine.lastCoeff t

def weight {n : Nat} (a : Atom (n + 1)) : Nat :=
  if leading a = 0 then 1 else (leading a).natAbs

/-- A positive common multiple, deliberately a product rather than an LCM.
This conservative normalization is total; no coefficient search is performed. -/
def coefficientModulus {n : Nat} (p : QF (n + 1)) : Nat := (p.atoms.map weight).prod

def nonzeroSign (a : Int) : Sign := if 0 < a then .pos else .neg

def adjustAtom {n : Nat} (M : Nat) : Atom (n + 1) → UnitAtom n
  | .nonneg t =>
    let a := Affine.lastCoeff t
    if a = 0 then .nonneg .zero (Affine.dropLast t)
    else .nonneg (nonzeroSign a)
      (Affine.scale ((M / a.natAbs : Nat) : Int) (Affine.dropLast t))
  | .dvd m t =>
    let a := Affine.lastCoeff t
    if a = 0 then .dvd m .zero (Affine.dropLast t)
    else
      let k := M / a.natAbs
      .dvd ((m + 1) * k - 1) (nonzeroSign a)
        (Affine.scale (k : Int) (Affine.dropLast t))

def adjust {n : Nat} (M : Nat) (p : QF (n + 1)) : UnitFormula n := p.map (adjustAtom M)

/-- `M | y` is retained. Omitting this guard would change the solution set. -/
def normalize {n : Nat} (p : QF (n + 1)) : UnitFormula n :=
  let M := coefficientModulus p
  .conj (.atom (.dvd (M - 1) .pos (Affine.const 0))) (adjust M p)

/-- Actual finite elimination for arbitrary affine coefficients; the separate
unit eliminator adds the essential nonnegative-witness guard. -/
def eliminate {n : Nat} (p : QF (n + 1)) : QF n := CotreePresburgerUnit.eliminate (normalize p)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize
