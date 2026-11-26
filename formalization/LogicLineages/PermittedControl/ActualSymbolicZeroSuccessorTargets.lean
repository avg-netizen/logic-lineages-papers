module
public import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanTargets
public import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroSuccessorMarkedClass (Marked decorate actualMarked)
open ActualZeroSuccessorPrefixPlan (PrefixSyntax erase countPlan cohortSyntax leastSyntax)
open ActualZeroClassCohortTransfer (SurvivingPrefix)
open ActualCountOriginDispositions (MovedAt)
open ActualZeroClassReplacement (Read replaceRow)
open ActualZeroClassRecombinedRow (outsideCohort)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations CountTailReady)
open ActualShortCountCleanup (shortLength retained shortShift)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs Matches)
open ActualFullValueMaximalMetadata (classFlags)
open ActualReadChargeIteration (ReadState ZeroEdge)
open ActualFiniteSignedNodeBranch (nodeCoefficient nodeLabels)
open ActualRankedNormalizationSyntax (normalizedTerms)

structure SyntaxState where
  constant : Int
  terms : List WeightedOperand

def kept (m : Marked) : Bool := decide (m.1.1 ≠ 0) && !m.2

def outsideSyntax (ms : List Marked) : List WeightedOperand :=
  (ms.filter kept).map Prod.fst

/-- Selected count correction from the literal source interval.
Genuine identity and long prefixes both contribute kappa; a positive
short prefix contributes its own literal length as well. A selected
invalid count or a selected bare coordinate is rejected. -/
noncomputable def originShift (m : Marked) : Option Int :=
  if m.2 then
    match m.1.2 with
    | .count _ lam mu =>
      let κ := Targets.countCoreConstant mu.1.repr
      match countPlan lam mu with
      | .identity | .survives _ => some (m.1.1 * κ)
      | .short _ k => some (m.1.1 * (κ + (k : Int)))
      | .invalid => none
    | .ordinary .. => some 0
    | .coordinate _ => none
  else some 0

noncomputable def originShifts : List Marked → Option Int
  | [] => some 0
  | m::ms => do
      let a ← originShift m
      let b ← originShifts ms
      pure (a+b)

noncomputable def anchorTerm (a : PrefixSyntax) (w : Int) : WeightedOperand :=
  (w,.count a.rank a.lam a.eta)

noncomputable def movedTerm (a p : PrefixSyntax) : WeightedOperand :=
  (-p.weight,ConcreteCountPairReplacement.replacementOperand a.rank p.lam p.eta a.lam a.eta)

noncomputable def moveOne (a p : PrefixSyntax) : List WeightedOperand :=
  if p.rank = a.rank then [anchorTerm a p.weight]
  else [anchorTerm a p.weight,movedTerm a p]

noncomputable def movedSyntax : Option PrefixSyntax → List PrefixSyntax → List WeightedOperand
  | none,_ => []
  | some a,ps => ps.flatMap (moveOne a)

def cleanSyntax (terms : List WeightedOperand) : List WeightedOperand :=
  terms.filter (fun t => decide (shortLength t.2 = 0))

def cleanupShift : List WeightedOperand → Int
  | [] => 0
  | t::ts => t.1 * (shortLength t.2 : Int) + cleanupShift ts

noncomputable def successorFromMarks (constant : Int) (ms : List Marked) : Option SyntaxState := do
  let shift ← originShifts ms
  let ps := cohortSyntax ms
  let before := outsideSyntax ms ++ movedSyntax (leastSyntax ps) ps
  pure ⟨constant + shift + cleanupShift before,cleanSyntax before⟩

/-- Only a zero branch with exactly parsed mask and valid origin plans
has a syntax successor. No values, first-hit counts, or raw valuation
are inputs to this typed plan. -/
noncomputable def successor (constant : Int) (raw : List WeightedOperand)
    (a : List Answer) : Option SyntaxState := do
  if nodeCoefficient raw a = 0 then
    let ms ← decorate (normalizedTerms raw) (classFlags (nodeLabels raw) a)
    successorFromMarks constant ms
  else none

def ExactMovedAndCleanupSyntax : Prop :=
  (∀ (f ρ : Nat → Nat) (a : Option SurvivingPrefix) (ps : List SurvivingPrefix) (moved : List Read),
    MovedAt f ρ a ps moved →
    moved.map Prod.fst = movedSyntax (a.map erase) (ps.map erase)) ∧
  ∀ before : List Read,
    (retained before).map Prod.fst = cleanSyntax (before.map Prod.fst) ∧
    shortShift before = cleanupShift (before.map Prod.fst)

def ExactOutsideAndOriginShiftSyntax : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (C : Nat) (terms : List WeightedOperand)
    (values : List Nat) (anns : List Annotation),
    AlignedAnnotations f θ terms values anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady θ t.2) →
    outsideSyntax (actualMarked f C terms anns) = (outsideCohort f C terms values anns).map Prod.fst ∧
    originShifts (actualMarked f C terms anns) = some (replaceRow f C terms values anns).2

/-- Same actual strong zero edge, with no substituted witness, and the
exact same finite comparison candidate. Erasing only numeric read values
identifies the true output with the source-static typed successor. -/
def ExactActualSymbolicZeroSuccessor : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (r top : Nat) (source out : ReadState)
    (raw : List WeightedOperand) (a : List Answer),
    source.reads.map Prod.fst = raw →
    ZeroEdge f B θ r top source out →
    Matches f θ (pairs (nodeLabels raw)) a →
    successor source.constant raw a = some ⟨out.constant,out.reads.map Prod.fst⟩

def FullActualSymbolicZeroSuccessor : Prop :=
  ExactMovedAndCleanupSyntax ∧ ExactOutsideAndOriginShiftSyntax ∧ ExactActualSymbolicZeroSuccessor

end LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
