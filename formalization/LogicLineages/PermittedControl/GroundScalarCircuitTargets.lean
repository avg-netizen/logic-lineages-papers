module
public import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryTargets
public import LogicLineages.PermittedControl.SelectedGeneratedSourceDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarHeadNote scalarCode)
open OriginalPrintedCircuitSequential (Gate Topological)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open SelectedGeneratedSource (scalarValueWith)

/-- Raw input `i` lives at the even name `2i`; a raw value `v` there stands for the positive input `v+1`. -/
def inputName (i : Nat) : Nat := 2 * i

/-- Circuit node number `k` lives at the odd name `2k+1`. -/
def nodeName (k : Nat) : Nat := 2 * k + 1

/-- Compile one scalar from node counter `k`: (gates, output name, next counter).
A variable reads its shared input name; `one`, the successor shift of a
variable, and sums are natural affine gates; a shift is one fixed-head
collapse wire whose head is the accepted notation `scalarHeadNote c`. -/
def circuitOf {ι : Type} (index : ι → Nat) : Scalar ι → Nat → List Gate × Nat × Nat
  | .one,k => ([.base (.affine (1,[]) (nodeName k))],nodeName k,k+1)
  | .var x,k => ([.base (.affine (1,[(1,inputName (index x))]) (nodeName k))],nodeName k,k+1)
  | .add a b,k =>
      let A := circuitOf index a k
      let B := circuitOf index b A.2.2
      (A.1 ++ B.1 ++ [.base (.affine (0,[(1,A.2.1),(1,B.2.1)]) (nodeName B.2.2))],
        nodeName B.2.2,B.2.2+1)
  | .shift c a,k =>
      let A := circuitOf index a k
      (A.1 ++ [.base (.collapse ⟨scalarHeadNote c,A.2.1,nodeName A.2.2⟩)],nodeName A.2.2,A.2.2+1)

/-- Counterexample relation tags (Opus A's M4 interface, verbatim): 0 is `y < x`
(E_A > E_B), 1 is `y ≤ x` (E_A ≥ E_B), and any other tag is `x ≠ y`. -/
def Counter (tag : Nat) (x y : Nat) : Prop :=
  if tag = 0 then y < x else if tag = 1 then y ≤ x else x ≠ y

/-- `-1 + x_hi - x_lo ≥ 0`, i.e. node `lo` is strictly below node `hi`. -/
def strictRow (lo hi : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-1,[(1,.variable hi),(-1,.variable lo)]))

/-- `x_hi - x_lo ≥ 0`. -/
def weakRow (lo hi : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (0,[(1,.variable hi),(-1,.variable lo)]))

/-- The matrix of `Counter tag x y` for left node `a` (x) and right node `b` (y). -/
def counterFormula (tag a b : Nat) : NormalForm.Formula :=
  if tag = 0 then strictRow b a
  else if tag = 1 then weakRow b a
  else .disjunction (strictRow a b) (strictRow b a)

structure Block where
  known : List Nat
  gates : List Gate
  matrix : NormalForm.Formula

/-- One closed block for the counterexample query: both circuits share the
input names; the right circuit continues the node counter of the left one.
The known list is every input name up to the sum of the two scalar codes. -/
def block {ι : Type} (index : ι → Nat) (tag : Nat) (A B : Scalar ι) : Block :=
  let CA := circuitOf index A 0
  let CB := circuitOf index B CA.2.2
  ⟨(List.range (scalarCode index A + scalarCode index B + 1)).map inputName,CA.1 ++ CB.1,
    counterFormula tag CA.2.1 CB.2.1⟩

def BlockShape : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (tag : Nat) (A B : Scalar ι),
    Topological (block index tag A B).known (block index tag A B).gates ∧
      PlainPreparedFormula (block index tag A B).matrix

/-- Existential correctness at every selected control. The circuit's raw
inputs range over all of ℕ; the scalar inputs are positive, one per index. -/
def BlockCorrect : Prop :=
  ∀ (f : Nat → Nat) (K : Nat), SelectedWithThreshold f K →
  ∀ (ι : Type) (index : ι → Nat) (tag : Nat) (A B : Scalar ι),
    (HasSuccessfulObservation f (block index tag A B).gates (block index tag A B).matrix true ↔
      ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧
        Counter tag (scalarValueWith f (fun x => ν (index x)) A) (scalarValueWith f (fun x => ν (index x)) B))

def FullGroundScalarCircuit : Prop := BlockShape ∧ BlockCorrect

end LogicLineages.PermittedControl.GroundScalarCircuit
