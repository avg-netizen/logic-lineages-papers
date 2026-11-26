module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets
public import LogicLineages.PermittedControl.SelectedCountOnlyClassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassReplacement
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open SelectedCountOnlyClass (prefixTarget)

abbrev Read := WeightedOperand × Nat

/-- The printed extra affordability condition is needed only when a
selected proper prefix is recognized as short. -/
def PrefixTailReady (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (t : WeightedOperand) : Annotation → Prop
  | .count i q _ =>
      match t.2 with
      | .count rank lam mu =>
          let η := prefixTarget mu
          f q = C → i ≠ 0 → 0 < shortGapLength lam η →
            max (actualOrdinalNorm lam.1.repr)
              (max (actualOrdinalNorm η.1.repr + 3) (max 1 B)) ≤ ρ rank
      | _ => True
  | _ => True

def Ready (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat) :
    List WeightedOperand → List Annotation → Prop
  | [],[] => True
  | t::terms,a::annotations => PrefixTailReady f B ρ C t a ∧ Ready f B ρ C terms annotations
  | _,_ => False

/-- Remove the chosen ordinary occurrences, preserve all signed count
corrections, and keep each surviving proper long prefix at its old rank.
Identities and recognized short prefixes contribute to the constant. -/
noncomputable def replaceOccurrence (f : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) :
    Annotation → Option Read × Int
  | .zeroWeight => (none,0)
  | .linear => (some (t,v),0)
  | .ordinary q => if f q = C then (none,0) else (some (t,v),0)
  | .count i q κ =>
      if f q = C then
        match t.2 with
        | .count rank lam mu =>
            let η := prefixTarget mu
            let k := shortGapLength lam η
            if i = 0 then (none,t.1 * κ)
            else if k = 0 then (some ((t.1,.count rank lam η),i),t.1 * κ)
            else (none,t.1 * κ + t.1 * (k : Int))
        | _ => (some (t,v),0)
      else (some (t,v),0)

noncomputable def replaceRow (f : Nat → Nat) (C : Nat) :
    List WeightedOperand → List Nat → List Annotation → List Read × Int
  | t::terms,v::values,a::annotations =>
      let head := replaceOccurrence f C t v a
      let tail := replaceRow f C terms values annotations
      (head.1.toList ++ tail.1,head.2 + tail.2)
  | _,_,_ => ([],0)

def liftedReads (f : Nat → Nat) (ρ : Nat → Nat) (reads : List Read) : Prop :=
  orderedReads f ρ (reads.map Prod.fst) (reads.map Prod.snd)

def readSum (reads : List Read) : Int :=
  actualSum (reads.map Prod.fst) (reads.map Prod.snd)

def ExactPrefixRead : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote) (v i : Nat),
    LowerOperandActual f ρ (.count rank lam mu) v →
    let η := prefixTarget mu
    η.1.repr ≤ lam.1.repr → FirstEntry f (countInitial lam.1.repr (ρ rank)) η.1.repr i →
    (i = 0 ↔ η.1.repr = lam.1.repr) ∧
    (i ≠ 0 → LowerOperandActual f ρ (.count rank lam η) i ∧
      lowerOperandRead f ρ (.count rank lam η) = some (some i))

def ExactRetainedRemainder : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations → Ready f B ρ C terms annotations →
    let out := replaceRow f C terms values annotations
    liftedReads f ρ out.1 ∧ out.2 + readSum out.1 = (rowParts f C terms values annotations).2

def ExactZeroClassReplacement : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (z C : Nat) (c : Int) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations → Ready f B ρ C terms annotations →
    (∀ t ∈ terms, ρ t.2.rank ≤ z) →
    C ∈ fullValues f annotations → (∀ D ∈ fullValues f annotations, D ≤ C) → f z ≤ C →
    (rowParts f C terms values annotations).1 = 0 →
    let out := replaceRow f C terms values annotations
    liftedReads f ρ out.1 ∧ c + actualSum terms values = (c + out.2) + readSum out.1

def FullActualZeroClassReplacement : Prop :=
  ExactPrefixRead ∧ ExactRetainedRemainder ∧ ExactZeroClassReplacement

end LogicLineages.PermittedControl.ActualZeroClassReplacement
