module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRows

/-- A signed parameter constant and the ORIGINAL remaining summand occurrences.
The two expanded terms are evaluated at the same retained valuation. They are
not new names with existentially independent values. -/
abbrev Row := (Term × Term) × List (Int × NormalForm.Summand)

def rowValue (r : Row) (ν : Nat → Nat) : Int :=
  (r.1.1.value ν : Int) - (r.1.2.value ν : Int) +
    (r.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum
def Row.variables (r : Row) : List Nat :=
  r.1.1.variables ++ r.1.2.variables ++ r.2.map (fun a => a.2.name)
def Row.parameters (r : Row) : List Nat := r.1.1.variables ++ r.1.2.variables

def Row.ofOriginal (r : NormalForm.Row) : Row :=
  ((.numeral r.1.toNat, .numeral (-r.1).toNat), r.2)

def positiveTerm (r : Row) : Term :=
  .add r.1.1 (r.2.foldr (fun a rest =>
    .add (.multiply a.1.toNat a.2.term) rest) (.numeral 0))
def negativeTerm (r : Row) : Term :=
  .add r.1.2 (r.2.foldr (fun a rest =>
    .add (.multiply (-a.1).toNat a.2.term) rest) (.numeral 0))
def absoluteTerm (r : Row) : Term :=
  .add (.subtract (positiveTerm r) (negativeTerm r))
    (.subtract (negativeTerm r) (positiveTerm r))

/-- The source current-occurrence partition is literal. Even a zero-weight
occurrence is moved into both parameter terms rather than silently erased.
All remaining occurrences retain their order, multiplicity, shifts and weights. -/
def substituteEntries (i : Nat) (replacement positive negative : Term) :
    List (Int × NormalForm.Summand) → Row
  | [] => ((positive, negative), [])
  | a :: entries =>
      let r := substituteEntries i replacement positive negative entries
      if a.2.name = i then
        ((.add (.multiply a.1.toNat (a.2.term.substitute i replacement)) r.1.1,
          .add (.multiply (-a.1).toNat (a.2.term.substitute i replacement)) r.1.2), r.2)
      else (r.1, a :: r.2)

def Row.substitute (i : Nat) (replacement : Term) (r : Row) : Row :=
  substituteEntries i replacement (r.1.1.substitute i replacement)
    (r.1.2.substitute i replacement) r.2

inductive Atom where
  | nonnegative (row : Row)
  | divisible (modulusMinusOne : Nat) (row : Row)
def Atom.row : Atom → Row
  | .nonnegative r | .divisible _ r => r
def Atom.eval (ν : Nat → Nat) : Atom → Prop
  | .nonnegative r => 0 ≤ rowValue r ν
  | .divisible m r => ((m + 1 : Nat) : Int) ∣ rowValue r ν
def Atom.substitute (i : Nat) (replacement : Term) : Atom → Atom
  | .nonnegative r => .nonnegative (r.substitute i replacement)
  | .divisible m r => .divisible m (r.substitute i replacement)
def Atom.compile : Atom → Matrix
  | .nonnegative r => atMost (negativeTerm r) (positiveTerm r)
  | .divisible m r => .divisible (m + 1) (absoluteTerm r)
def Atom.ofOriginal : NormalForm.Atom → Atom
  | .nonnegative r => .nonnegative (.ofOriginal r)
  | .divisible m r => .divisible m (.ofOriginal r)

inductive Formula where
  | truth | falsity
  | atom (a : Atom)
  | negative (p : Formula)
  | conjunction (p q : Formula)
  | disjunction (p q : Formula)
def Formula.eval (ν : Nat → Nat) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .atom a => a.eval ν
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .disjunction p q => p.eval ν ∨ q.eval ν
def Formula.compile : Formula → Matrix
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => a.compile
  | .negative p => .negative p.compile
  | .conjunction p q => .conjunction p.compile q.compile
  | .disjunction p q => .disjunction p.compile q.compile
def Formula.variables : Formula → List Nat
  | .truth | .falsity => []
  | .atom a => a.row.variables
  | .negative p => p.variables
  | .conjunction p q | .disjunction p q => p.variables ++ q.variables
def Formula.parameters : Formula → List Nat
  | .truth | .falsity => []
  | .atom a => a.row.parameters
  | .negative p => p.parameters
  | .conjunction p q | .disjunction p q => p.parameters ++ q.parameters
def Formula.substitute (i : Nat) (replacement : Term) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (a.substitute i replacement)
  | .negative p => .negative (p.substitute i replacement)
  | .conjunction p q => .conjunction (p.substitute i replacement) (q.substitute i replacement)
  | .disjunction p q => .disjunction (p.substitute i replacement) (q.substitute i replacement)
def Formula.ofOriginal : NormalForm.Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (.ofOriginal a)
  | .negative p => .negative (.ofOriginal p)
  | .conjunction p q => .conjunction (.ofOriginal p) (.ofOriginal q)
  | .disjunction p q => .disjunction (.ofOriginal p) (.ofOriginal q)

/-- The entire quantified block is excluded from parameter constants. Bound
summands remain in the occurrence list and are NOT excluded by this invariant. -/
def ParametersIndependent (bound : List Nat) (p : Formula) : Prop :=
  ∀ i ∈ bound, i ∉ p.parameters

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRows
