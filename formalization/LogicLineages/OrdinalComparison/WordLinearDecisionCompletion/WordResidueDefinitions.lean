module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Definitions
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue
open PolynomialGraphCompletion

/-- An affine residue s*t+b. Shift-only words retain slope one. -/
abbrev Affine := Int × Int

def letterAffine (m : Nat) (a : Letter) : Affine :=
  if a.1 = 0 then (1, a.2.2.2)
  else if a.1 = 4 then (0, kernelCounterResidue a.2.1 a.2.2.1 m)
  else (0, fastControlResidue m)

/-- Pay literal domains and the input bound for the final Phi application.
Only E uses the independently scheduled source-count residue supplier. -/
def letterTail (m : Nat) (a : Letter) : Nat :=
  WordGuardCompletion.letterTail a + m +
    if a.1 = 4 then KernelSourceCompletion.residueTail a.2.1 a.2.2.1 0 m else 0

/-- Compose in the actual source evaluation order, including signed shifts
after the last nonlinear letter as INTEGER offsets. -/
def affine (m : Nat) : Word → Affine
  | [] => (1, 0)
  | a :: w =>
      let p := letterAffine m a
      let q := affine m w
      (q.1 * p.1, q.1 * p.2 + q.2)

/-- The offset pays the suffix threshold at its actual reached argument. -/
def tail (m : Nat) : Word → Nat
  | [] => 0
  | a :: w => letterTail m a + WordGuardCompletion.letterOffset a + tail m w

/-- Every source occurrence keeps its original raw name. Even a zero-slope
occurrence remains as a zero-coefficient raw summand, preserving support. -/
def row (m : Nat) (r : Row) : Row :=
  (r.1 + (r.2.map (fun a => a.1 * (affine m a.2.2).2)).sum,
    r.2.map (fun a => (a.1 * (affine m a.2.2).1, (a.2.1, []))))

def rowTail (m : Nat) (r : Row) : Nat :=
  (r.2.map (fun a => tail m a.2.2)).sum

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue
