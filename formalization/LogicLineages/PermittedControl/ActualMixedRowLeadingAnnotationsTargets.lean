module
public import LogicLineages.PermittedControl.ActualCountLeadingErrorTargets
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open Targets (countCoreConstant)

inductive Annotation where
  | zeroWeight
  | linear
  | ordinary (q : Nat)
  | count (i q : Nat) (κ : Int)

def fullValue (f : Nat → Nat) : Annotation → Option Nat
  | .zeroWeight | .linear => none
  | .ordinary q | .count _ q _ => some (f q)

def fullValues (f : Nat → Nat) (annotations : List Annotation) : List Nat :=
  annotations.filterMap (fullValue f)

def NonlinearOperand : LowerOperand → Prop
  | .coordinate _ => False
  | .ordinary _ F => SelectedNonlinearImageBounds.NonlinearField F
  | .count _ _ _ => True

/-- The count annotation is used after the original short counts have been
removed. The actual lower bound is imposed on each surviving count. -/
def CountTailReady (ρ : Nat → Nat) : LowerOperand → Prop
  | .count rank lam mu =>
    LongField (.entry 0 lam mu) ∧
      max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3) ≤ ρ rank
  | _ => True

def LinearOperand : LowerOperand → Prop
  | .coordinate _ | .ordinary _ (.iterate 0) => True
  | _ => False

def ActualAnnotation (f : Nat → Nat) (ρ : Nat → Nat) (t : WeightedOperand)
    (v : Nat) : Annotation → Prop
  | .zeroWeight => t.1 = 0
  | .linear => t.1 ≠ 0 ∧ LinearOperand t.2 ∧ v = ρ t.2.rank
  | .ordinary q =>
    t.1 ≠ 0 ∧ ∃ rank F, t.2 = .ordinary rank F ∧
      SelectedNonlinearImageBounds.NonlinearField F ∧ ρ rank ≤ q ∧ v = f q
  | .count i q κ =>
    t.1 ≠ 0 ∧ ∃ rank lam mu, t.2 = .count rank lam mu ∧
      let x := ρ rank
      let A := countInitial lam.1.repr x
      let η := mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})
      η ≤ lam.1.repr ∧ FirstEntry f A η i ∧ q = entryNormAt f A i ∧
        q = f^[i] x ∧ x + i ≤ q ∧ κ = countCoreConstant mu.1.repr ∧
        2 * (v : Int) = (f q : Int) + 2 * ((i : Int) + κ) ∧
        ∀ D : Nat, f q ≤ D → ((i : Int) + κ).natAbs ≤ Nat.log2 D + κ.natAbs

/-- Keep each actual original read in its position, including repeated
operands and operands whose signed coefficient vanishes. -/
inductive AlignedAnnotations (f : Nat → Nat) (ρ : Nat → Nat) :
    List WeightedOperand → List Nat → List Annotation → Prop
  | nil : AlignedAnnotations f ρ [] [] []
  | cons {t terms v values ann annotations} :
      LowerOperandActual f ρ t.2 v →
      lowerOperandRead f ρ t.2 = some (some v) →
      ActualAnnotation f ρ t v ann →
      AlignedAnnotations f ρ terms values annotations →
      AlignedAnnotations f ρ (t :: terms) (v :: values) (ann :: annotations)

def BuildActualAnnotations : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat),
    orderedReads f ρ terms values →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    ∃ annotations, AlignedAnnotations f ρ terms values annotations

/-- The active nonlinear occurrence at the greatest raw coordinate pays
the genuine maximum. No assumption on the maximum class's signed sum is needed. -/
def LargestActualFull : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (zRank : Nat) (terms : List WeightedOperand) (values : List Nat),
    orderedReads f ρ terms values →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    (∀ t ∈ terms, ρ t.2.rank ≤ ρ zRank) →
    (∃ t ∈ terms, t.1 ≠ 0 ∧ t.2.rank = zRank ∧ NonlinearOperand t.2) →
    ∃ annotations C, AlignedAnnotations f ρ terms values annotations ∧
      (fullValues f annotations).max? = some C ∧ C ∈ fullValues f annotations ∧
      (∀ D ∈ fullValues f annotations, D ≤ C) ∧ f (ρ zRank) ≤ C

def FullActualMixedRowLeadingAnnotations : Prop :=
  BuildActualAnnotations ∧ LargestActualFull

end LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
