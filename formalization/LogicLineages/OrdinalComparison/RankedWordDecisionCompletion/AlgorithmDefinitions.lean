module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.ContractDefinitions
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankDefinitions
public import LogicLineages.OrdinalComparison.RangePhiFactorization.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Algorithm
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open WordLinearDecisionCompletion

abbrev Item := Int × (Nat × Word)
abbrev Labelled := Item × Nat

def foldMax (xs : List Nat) : Nat := xs.foldr max 0
def rowTail (r : Row) : Nat := foldMax (r.2.map (fun a => wordTail a.2.2))

/-- Every stage uses literal shift extraction and drops coefficient-zero
occurrences only after the original row's domain tail has been recorded. -/
def canonicalRow (r : Row) : Row :=
  let out := normalizeRow r
  (out.1,out.2.filter (fun a => a.1 != 0))

def active (r : Row) : List Item := r.2.filter (fun a => !a.2.2.isEmpty)
def linearPart (r : Row) : List Item := r.2.filter (fun a => a.2.2.isEmpty)
def hasMaximum (maximum : Nat) (r : Row) : Bool :=
  (active r).any (fun a => a.2.1 == maximum)

def head (a : Item) : Letter := a.2.2.getLastD phiLetter
def innerWord (a : Item) : Word := a.2.2.dropLast
def isCounter (a : Item) : Bool := (head a).1 == 4
def counterIndex (a : Item) : Nat := (head a).2.1-3
def mass (a : Item) : Nat := (head a).2.2.1
def rank (a : Item) : Nat := topRank a.2.2

def leader (a : Item) : Token :=
  (a.2.1,if isCounter a then leaderValueWord (innerWord a) (counterIndex a) (mass a)
    else a.2.2)

def preimage (a : Item) : Word :=
  if isCounter a then innerWord a ++ leaderWord (counterIndex a) (mass a)
  else if (head a).1 = 1 then innerWord a
  else innerWord a ++ [RangePhiFactorization.predecessorHead (head a)]

def sourceTail (a : Item) : Nat :=
  max (wordTail a.2.2)
    (if isCounter a then
      max (expansionTail (innerWord a) (counterIndex a) (mass a))
        (reachTail (innerWord a) (CounterLeaderBounds.threshold (counterIndex a) (mass a)))
    else if (head a).1 = 1 then wordTail (innerWord a)
    else RangePhiFactorization.wordFactorTail (innerWord a) (head a))

def collisionTail (a b : Item) : Nat :=
  if isCounter a && isCounter b then
    max (reachTail (innerWord a) (scalarTail (counterIndex a) (mass a) (mass b) 0 0))
      (reachTail (innerWord b) (scalarTail (counterIndex b) (mass b) (mass a) 0 0))
  else 0

def rowSourceTail (r : Row) : Nat :=
  max (rowTail r)
    (max (foldMax ((active r).map sourceTail))
      (foldMax ((active r).flatMap (fun a => (active r).map (collisionTail a)))))

def nonlinearMass (r : Row) : Nat := ((active r).map (fun a => a.1.natAbs)).sum
def linearMass (r : Row) : Nat := ((linearPart r).map (fun a => a.1.natAbs)).sum
def preimageOffset (r : Row) : Nat := ((active r).map (fun a => wordOffset (preimage a))).sum

/-- Sufficient arithmetic payment for the paid Phi multiplicative step gap
and quadratic gap. No tower is evaluated by this threshold constructor. -/
def signPayment (r : Row) : Nat :=
  let S := nonlinearMass r
  let A := linearMass r
  let M := preimageOffset r
  let B := r.1.natAbs
  64*(S+A+A*M+B+1)

def signTail (r : Row) : Nat :=
  max (rowSourceTail r)
    (foldMax ((active r).map (fun a => reachTail (preimage a) (signPayment r))))

/-- All finite label vectors are enumerated from syntax, independently of
source values. Labels specify an ordered equality partition; gaps are allowed. -/
def assignments (bound : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range bound).flatMap (fun label =>
      (assignments bound n).map (fun labels => label::labels))

def labelled (r : Row) (labels : List Nat) : List Labelled := (active r).zip labels
def leaderClass (xs : List Labelled) (label : Nat) : List Item :=
  (xs.filter (fun a => a.2 == label)).map Prod.fst

def classes (r : Row) (labels : List Nat) : List (List Item) :=
  ((List.range (active r).length).map (leaderClass (labelled r labels))).filter
    (fun xs => !xs.isEmpty)

def conjoin (ps : List Formula) : Formula := ps.foldr .conj .top

noncomputable def partitionGuard (D maximum : Nat) (r : Row) (labels : List Nat) : Formula :=
  let xs := labelled r labels
  conjoin (xs.flatMap (fun a => xs.map (fun b =>
    comparisonGuard D maximum (leader a.1) (leader b.1) (FullWordGuardCompletion.orderNat a.2 b.2))))

noncomputable def partitionTail (D maximum : Nat) (r : Row) : Nat :=
  max (rowSourceTail r)
    (foldMax ((active r).flatMap (fun a => (active r).map (fun b =>
      comparisonCutoff D maximum (leader a) (leader b)))))

def leading (xs : List Item) : Int :=
  (xs.map (fun a => a.1 * (if isCounter a then 1 else 2))).sum

def hasOrdinary (xs : List Item) : Bool := xs.any (fun a => !isCounter a)

def rowAdd (r s : Row) : Row := (r.1+s.1,r.2++s.2)

def ordinaryResidual (a : Item) : Row :=
  if isCounter a then
    (a.1*(1-(((mass a+1)/2 : Nat) : Int)),
      (residualWords (counterIndex a) (mass a)).map
        (fun p => (a.1,a.2.1,innerWord a++p.2)))
  else (0,[])

/-- Actual upper-chain counter words from the unchanged collision recursion.
Each emitted final head has rank strictly above the reference rank m+3. -/
def upperResidualWords : Nat → Nat → Nat → List (Nat × Word)
  | 0, _, _ => []
  | k+1, m, c =>
      (m+k+4,[counterLetter (m+k+4) (c+m+k+4)]) ::
        (upperResidualWords k m c).map (fun p =>
          (p.1,kernelLetter (m+k+4) (c+m+k+4) 0 :: p.2))

def leastRank (D : Nat) (xs : List Item) : Nat :=
  (xs.map rank).foldr min (D+1)

def counterResidual (reference : Nat) (a : Item) : Row :=
  (0,(upperResidualWords (rank a-reference) (reference-3) (mass a)).map
    (fun p => (a.1,a.2.1,innerWord a++p.2)))

/-- The source replacement is exact, with integer coefficients. The doubled
identity is used only in its proof; no global row scaling is performed. -/
def classReplacement (D : Nat) (xs : List Item) : Row :=
  if hasOrdinary xs then (xs.map ordinaryResidual).foldr rowAdd (0,[])
  else (xs.map (counterResidual (leastRank D xs))).foldr rowAdd (0,[])

def outside (r : Row) (labels : List Nat) (removed : Nat) : List Item :=
  linearPart r ++ ((labelled r labels).filter (fun a => a.2 != removed)).map Prod.fst

def rewrite (D : Nat) (r : Row) (labels : List Nat) (removed : Nat) : Row :=
  let replacement := classReplacement D (leaderClass (labelled r labels) removed)
  (r.1+replacement.1,outside r labels removed ++ replacement.2)

def zeroClass (r : Row) (labels : List Nat) : Option Nat :=
  (List.range (active r).length).find? (fun label =>
    let xs := leaderClass (labelled r labels) label
    !xs.isEmpty && leading xs == 0)

inductive Action where
  | finish (outcome : Outcome)
  | descend (row : Row)

structure Branch where
  tail : Nat
  guard : Formula
  action : Action

/-- One finite, completely syntax-directed partition/cancellation stage.
Every zero-leading branch emits the literal class rewrite above. No semantic
comparison is queried to choose a branch or decide whether its guard holds. -/
noncomputable def partitionBranch (D maximum : Nat) (r : Row) (labels : List Nat) : Branch :=
  let guard := partitionGuard D maximum r labels
  match zeroClass r labels with
  | some removed =>
      ⟨partitionTail D maximum r,guard,.descend (rewrite D r labels removed)⟩
  | none =>
      let greatest := (classes r labels).getLastD []
      let sign := if leading greatest < 0 then 0 else 2
      ⟨max (partitionTail D maximum r) (signTail r),guard,.finish ⟨sign,(0,[])⟩⟩

/-- The original row's literal domains are paid before canonicalization can
remove a zero occurrence or any signed outer shift. -/
noncomputable def stage (D maximum : Nat) (r : Row) : List Branch :=
  let originalTail := rowTail r
  let current := canonicalRow r
  if hasMaximum maximum current then
    (assignments (active current).length (active current).length).map (fun labels =>
      let out := partitionBranch D maximum current labels
      {out with tail := max originalTail out.tail})
  else [⟨max originalTail (rowSourceTail current),.top,.finish ⟨3,current⟩⟩]

noncomputable def stageCutoff (D maximum : Nat) (r : Row) : Nat :=
  foldMax ((stage D maximum r).map Branch.tail)

abbrev EncodedBranch := Nat × Nat × (Nat × (Nat × Row))

def encodeBranch (b : Branch) : EncodedBranch :=
  (b.tail,Formula.encode b.guard,match b.action with
    | .finish o => (0,o.tag,o.row)
    | .descend r => (1,0,r))

/-- Intrinsic top-level histogram of every actual current source row term.
Arguments of a top-level counter are not separate row atoms. -/
def rowMeasure (D : Nat) (r : Row) : ComparisonKernelHistogram (D+1) :=
  comparisonKernelHistogram (D+1) (rowRankList r)

def RowLess (D : Nat) (next current : Row) : Prop :=
  ComparisonKernelHistogramLt (D+1) (rowMeasure D next) (rowMeasure D current)

def BranchSyntax (D maximum : Nat) (names : List Nat) (b : Branch) : Prop :=
  Formula.allowed D b.guard ∧ linear maximum b.guard = true ∧
  FormulaNamesFrom names b.guard ∧
  match b.action with
  | .finish o => RowAllowed D o.row ∧ NamesFrom names o.row ∧
      (o.tag = 0 ∨ o.tag = 2 ∨ (o.tag = 3 ∧ LinearRow maximum o.row))
  | .descend r => RowAllowed D r ∧ NamesFrom names r

noncomputable def BranchDomains (b : Branch) (ν : Nat → Nat) : Prop :=
  Formula.meaningful b.guard ν ∧
  match b.action with
  | .finish o => RowDomain o.row ν
  | .descend r => RowDomain r ν

noncomputable def BranchCorrect (maximum : Nat) (source : Row) (b : Branch)
    (ν : Nat → Nat) : Prop :=
  Formula.eval ν b.guard →
  match b.action with
  | .finish o => OutcomeCorrect maximum source o ν
  | .descend r => RowValue r ν = RowValue source ν

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Algorithm
