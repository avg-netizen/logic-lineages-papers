module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector
open GuardChildMeasureCompletion OuterShiftNormalization

/-- At a terminal pair, either the left side is a shifted leaf or the
right side is a shifted leaf below a nonlinear left side. -/
def terminalRow (p : WordPair) : Row :=
  if coreWord p.1 = [] then
    (shiftSum p.1,[(1,0,[]),(-1,1,p.2)])
  else (1,[])

/-- Pay literal domains on both sides. The reversed growth payment is
needed to decide the same-variable leaf/nonlinear case independently of x. -/
def terminalTail (p : WordPair) : Nat :=
  max (leafPairTail p.1 p.2)
    (if coreWord p.1 = [] then
      if coreWord p.2 = [] then 0 else nonlinearLeafTail p.2 p.1
    else nonlinearLeafTail p.1 p.2)

def terminalSame (p : WordPair) : Nat :=
  if coreWord p.1 = [] then
    if coreWord p.2 = [] then orderInt (shiftSum p.1) (shiftSum p.2) else 0
  else 2

/-- Literal finite list of all original and recursively generated pairs. -/
def finiteTrace (p : WordPair) (fuel : Nat) : List WordPair :=
  (List.range (fuel+1)).map (fun n => (run p n).1)

/-- Computed common cutoff, word-linear row, the three finite Boolean
guards, decided same-variable outcome, and the finite generated-word trace. -/
abbrev Package := Nat × Row × Guards × Nat × List WordPair
def packageTail (out : Package) : Nat := out.1
def packageRow (out : Package) : Row := out.2.1
def packageGuards (out : Package) : Guards := out.2.2.1
def packageSame (out : Package) : Nat := out.2.2.2.1
def packageTrace (out : Package) : List WordPair := out.2.2.2.2

def finish (p : WordPair) (fuel : Nat) : Package :=
  let s := run p fuel
  (max (paidTail s) (terminalTail s.1),terminalRow s.1,makeGuards s.2.2,
    liftTie s.2.2 (terminalSame s.1),finiteTrace p fuel)

def invalidPackage : Package := (0,(0,[]),makeGuards 1,1,[])

/-- Actual syntax-only compiler. Termination of the least search and its
total computability are separate frozen obligations. No raw input values
or semantic comparisons are arguments of this program. -/
noncomputable def compile (D : Nat) (p : WordPair) : Package :=
  if admitted D p = true then finish p (leastFuel D p) else invalidPackage

end LogicLineages.OrdinalComparison.FullWordGuardCompletion
