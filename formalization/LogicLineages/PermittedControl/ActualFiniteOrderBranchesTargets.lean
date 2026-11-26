module
public import LogicLineages.PermittedControl.ActualCoordinateRankChartTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteOrderBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

abbrev Entry := Nat × Nat
abbrev Pattern := Nat × List Entry

def choices (k : Nat) : List Nat → List (List Entry)
  | [] => [[]]
  | name :: names =>
    (List.range k).flatMap (fun rank => (choices k names).map (fun es => (name,rank) :: es))

def onto (k : Nat) (es : List Entry) : Bool :=
  (List.range k).all (fun rank => (es.map Prod.snd).contains rank)

/-- One entry per source occurrence. A repeated source name need not
be rejected by enumeration: any incompatible label fails the real guard. -/
def patterns (names : List Nat) : List Pattern :=
  (List.range (names.length+1)).flatMap (fun k =>
    ((choices k names).filter (onto k)).map (fun es => (k,es)))

def Dense (names : List Nat) (p : Pattern) : Prop :=
  p.1 ≤ names.length ∧ p.2.map Prod.fst = names ∧
    (∀ e ∈ p.2, e.2 < p.1) ∧
    ∀ j : Nat, j < p.1 → ∃ e ∈ p.2, e.2 = j

def signedGap (x y shift : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-(shift : Int),[(-1,.variable x),(1,.variable y)]))

def comparePair (a b : Entry) : NormalForm.Formula :=
  if a.2 = b.2 then .conjunction (signedGap a.1 b.1 0) (signedGap b.1 a.1 0)
  else if a.2 < b.2 then signedGap a.1 b.1 1
  else .truth

def allTrue (ps : List NormalForm.Formula) : NormalForm.Formula :=
  ps.foldr NormalForm.Formula.conjunction .truth

def guard (p : Pattern) : NormalForm.Formula :=
  allTrue (p.2.flatMap (fun a => p.2.map (comparePair a)))

def Compares (θ : Nat → Nat) (p : Pattern) : Prop :=
  ∀ a ∈ p.2, ∀ b ∈ p.2,
    (a.2 = b.2 → θ a.1 = θ b.1) ∧ (a.2 < b.2 → θ a.1 < θ b.1)

def look (key value : Entry → Nat) (j : Nat) : List Entry → Nat
  | [] => 0
  | e :: es => if key e = j then value e else look key value j es

def rename (p : Pattern) (name : Nat) : Nat :=
  look Prod.fst Prod.snd name p.2

def realized (θ : Nat → Nat) (p : Pattern) (rank : Nat) : Nat :=
  if rank < p.1 then look Prod.snd (fun e => θ e.1) rank p.2
  else p.2.foldr (fun e b => max (θ e.1) b) 0 + rank + 1

noncomputable def actualPattern (θ : Nat → Nat) (names : List Nat) : Pattern :=
  (ActualCoordinateRankChart.size θ names,names.map (fun name =>
    (name,ActualCoordinateRankChart.rankOf θ names name)))

def ExactPatternEnumeration : Prop :=
  ∀ (names : List Nat) (p : Pattern), p ∈ patterns names ↔ Dense names p

def ExactOrderGuard : Prop :=
  ∀ (θ : Nat → Nat) (p : Pattern), (guard p).eval θ ↔ Compares θ p

def ExactActualBranchCoverage : Prop :=
  ∀ (θ : Nat → Nat) (names : List Nat),
    actualPattern θ names ∈ patterns names ∧ (guard (actualPattern θ names)).eval θ

def ExactBranchRealization : Prop :=
  ∀ (θ : Nat → Nat) (names : List Nat) (p : Pattern), p ∈ patterns names → (guard p).eval θ →
    StrictMono (realized θ p) ∧
    (∀ e ∈ p.2, rename p e.1 = e.2 ∧ realized θ p e.2 = θ e.1) ∧
    ∀ name ∈ names, rename p name < p.1 ∧ realized θ p (rename p name) = θ name

def FullActualFiniteOrderBranches : Prop :=
  ExactPatternEnumeration ∧ ExactOrderGuard ∧ ExactActualBranchCoverage ∧ ExactBranchRealization

end LogicLineages.PermittedControl.ActualFiniteOrderBranches
