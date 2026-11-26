module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsTargets
public import LogicLineages.PermittedControl.SelectedLeadingSignCutoffTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingSum
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations
open Targets (countCoreConstant)

/-- The first projection is the doubled coefficient of the actual class
with full value C. The second projection is the signed remainder. -/
def contribution (f : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) :
    Annotation → Int × Int
  | .zeroWeight => (0,0)
  | .linear => (0,t.1 * (v : Int))
  | .ordinary q =>
      if f q = C then (2 * t.1,0) else (0,t.1 * (v : Int))
  | .count i q κ =>
      if f q = C then (t.1,t.1 * ((i : Int) + κ)) else (0,t.1 * (v : Int))

def rowParts (f : Nat → Nat) (C : Nat) :
    List WeightedOperand → List Nat → List Annotation → Int × Int
  | t::terms,v::values,a::annotations =>
      let head := contribution f C t v a
      let tail := rowParts f C terms values annotations
      (head.1 + tail.1,head.2 + tail.2)
  | _,_,_ => (0,0)

noncomputable def correctionBound : LowerOperand → Nat
  | .count _ _ mu => (countCoreConstant mu.1.repr).natAbs
  | _ => 0

def slopeBound (terms : List WeightedOperand) : Nat :=
  terms.foldr (fun t k => 2 * t.1.natAbs + k) 0

noncomputable def offsetBound (terms : List WeightedOperand) : Nat :=
  terms.foldr (fun t k => t.1.natAbs * correctionBound t.2 + k) 0

def correctionBoundCode (op : LowerOperandCode) : Nat :=
  if op.1 = 2 then
    (1 - (((rawNormCode op.2.2.2.2.2 + 1) / 2 : Nat) : Int)).natAbs
  else 0

def slopeBoundCode (terms : List WeightedCode) : Nat :=
  terms.foldr (fun t k => 2 * t.1.natAbs + k) 0

def offsetBoundCode (terms : List WeightedCode) : Nat :=
  terms.foldr (fun t k => t.1.natAbs * correctionBoundCode t.2 + k) 0

def rowCutoffCode (c : Int) (terms : List WeightedCode) : Nat :=
  SelectedLeadingSignCutoff.cutoff (slopeBoundCode terms) (c.natAbs + offsetBoundCode terms)

def ExactEffectiveCutoff : Prop :=
  Primrec₂ rowCutoffCode ∧
  ∀ c (terms : List WeightedOperand),
    rowCutoffCode c (terms.map encodeWeighted) =
      SelectedLeadingSignCutoff.cutoff (slopeBound terms) (c.natAbs + offsetBound terms)

/-- The original weighted row, at an actual largest class, has the exact
doubled decomposition even when the class coefficient is zero. -/
def ExactSignedDecomposition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (z C : Nat) (c : Int) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations →
    (∀ t ∈ terms, ρ t.2.rank ≤ z) →
    (∀ D ∈ fullValues f annotations, D ≤ C) →
    f z ≤ C →
    let parts := rowParts f C terms values annotations
    let R := c + actualSum terms values
    let E := c + parts.2
    2 * R = parts.1 * (C : Int) + 2 * E ∧
      E.natAbs ≤ slopeBound terms * Nat.log2 C + (c.natAbs + offsetBound terms)

def ExactNonzeroLeadingSign : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (zRank : Nat) (c : Int) (terms : List WeightedOperand)
    (values : List Nat),
    orderedReads f ρ terms values →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    (∀ t ∈ terms, ρ t.2.rank ≤ ρ zRank) →
    (∃ t ∈ terms, t.1 ≠ 0 ∧ t.2.rank = zRank ∧ NonlinearOperand t.2) →
    ∃ annotations C, AlignedAnnotations f ρ terms values annotations ∧
      (fullValues f annotations).max? = some C ∧
      let parts := rowParts f C terms values annotations
      let R := c + actualSum terms values
      rowCutoffCode c (terms.map encodeWeighted) ≤ ρ zRank →
      parts.1 ≠ 0 →
      (0 < R ↔ 0 < parts.1) ∧ (R < 0 ↔ parts.1 < 0) ∧
        (0 ≤ R ↔ 0 < parts.1) ∧ R ≠ 0

def FullActualMixedRowLeadingSum : Prop :=
  ExactEffectiveCutoff ∧ ExactSignedDecomposition ∧ ExactNonzeroLeadingSign

end LogicLineages.PermittedControl.ActualMixedRowLeadingSum
