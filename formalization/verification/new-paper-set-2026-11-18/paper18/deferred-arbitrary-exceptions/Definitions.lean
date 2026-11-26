module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Definitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphDomains
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion

/-- Literal finite presentation: input, output, cutoff, tail equation, points.
All wire names refer to ONE shared valuation. -/
abbrev Graph := Nat × Nat × Nat × Row × List (Nat × Nat)
def Graph.input (g : Graph) := g.1
def Graph.output (g : Graph) := g.2.1
def Graph.cutoff (g : Graph) := g.2.2.1
def Graph.tail (g : Graph) := g.2.2.2.1
def Graph.points (g : Graph) := g.2.2.2.2

noncomputable def Graph.holds (g : Graph) (ν : Nat → Nat) : Prop :=
  (g.cutoff ≤ ν g.input ∧ RowValue g.tail ν = 0) ∨
    ∃ p ∈ g.points, ν g.input = p.1 ∧ ν g.output = p.2

/-- Tail domain/degree certification is separate from graph functionality. -/
noncomputable def Graph.Valid (D : Nat) (g : Graph) : Prop :=
  RowAllowed D g.tail ∧
  (∀ ν : Nat → Nat, g.cutoff ≤ ν g.input → RowDomain g.tail ν) ∧
  (∀ p ∈ g.points, p.1 < g.cutoff)

noncomputable def Graph.Functional (g : Graph) (h : Nat → Nat) : Prop :=
  ∀ ν : Nat → Nat, g.holds ν ↔ ν g.output = h (ν g.input)

def LinearRow (r : Row) : Prop := ∀ a ∈ r.2, a.2.2 = []
def LinearFormula (p : Formula) : Prop := ∀ a ∈ p.tokens, a.2 = []
def boundRow (i n : Nat) : Row := (-(n : Int),[(1,i,[])])
def boundFormula (i n : Nat) : Formula := .atom (.nonnegative (boundRow i n))
def valueFormula (i n : Nat) : Formula := PolynomialBoolean.equality (boundRow i n)

def Graph.choices (g : Graph) : List Formula :=
  .conj (boundFormula g.input g.cutoff) (PolynomialBoolean.equality g.tail) ::
    g.points.map (fun p => .conj (valueFormula g.input p.1) (valueFormula g.output p.2))

/-- Positive Cartesian specialization. Unchosen tail words are absent from
these syntax trees, not hidden under an inactive Boolean disjunct. -/
def branches : List Graph → List Formula
  | [] => [.top]
  | g::gs => g.choices.flatMap (fun p => (branches gs).map (fun q => .conj p q))

def matrices (d : Nat) (gs : List Graph) (rs : List Row) (p : Formula) : List Formula :=
  (branches gs).map (fun q => .conj (PolynomialBoolean.positiveFormula d)
    (.conj q (.conj (PolynomialBoolean.graphFormula rs) p)))

noncomputable def SourceHolds (d : Nat) (gs : List Graph) (rs : List Row) (p : Formula)
    (ν : Nat → Nat) : Prop :=
  PolynomialBoolean.Positive d ν ∧ (∀ g ∈ gs, g.holds ν) ∧
    (∀ r ∈ rs, RowValue r ν = 0) ∧ Formula.eval ν p

abbrev QueryData := List Graph × List Row × Nat
def sourceCode (gs : List Graph) (rs : List Row) (p : Formula) : Nat :=
  Encodable.encode ((gs,rs,p.encode) : QueryData)

namespace Code
open PolynomialBoolean.Code

def choices (g : Graph) : List Nat :=
  conj (nonnegative (boundRow g.input g.cutoff)) (equal g.tail) ::
    g.points.map (fun p => conj (equal (boundRow g.input p.1)) (equal (boundRow g.output p.2)))
def branches : List Graph → List Nat
  | [] => [0]
  | g::gs => (choices g).flatMap (fun p => (branches gs).map (fun q => conj p q))
def decode (n : Nat) : QueryData := (Encodable.decode n).getD ([],[],0)
def package (d code : Nat) : List Nat :=
  let data := decode code
  (branches data.1).map (fun q => conj (positive d) (conj q (conj (graph data.2.1) data.2.2)))
/-- Each complete branch is solved separately; no global bank of tail words. -/
noncomputable def decide (D d code : Nat) : Bool :=
  (package d code).any (fun n => ClosedWordDecisionCompletion.Machine.solve D n)
end Code

def actualHead (code input output : Nat) : Graph :=
  (input,output,0,headEquation code input output,[])

end LogicLineages.StandardControlCurrent.GraphDomains
