module
public import LogicLineages.PermittedControl.ActualBitFamilyRawDriverTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
open ActualBitFamilyRawDriver (BoundProgram HighProgram solve)
open ActualBitFamilyRawLayout (encodeFamily names)
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (dimension)
open ActualBitFamilyExistentialLow (Satisfiable)
open ActualBitFamilyHigh (AllPaid)
open ActualNamedBitFamilyHigh (cutoff)
open ActualNamedBitFamilyCommonCutoffStep (low)

abbrev TypedHigh := Family → List Family

/-- The *new compiler's* ordered actual output has a typed witness. No
identity, permutation, or equality test with a former compiled tape occurs. -/
def Certified (f : Nat → Nat) (B : Nat) (bound : BoundProgram)
    (high : HighProgram) (typedHigh : TypedHigh) : Prop :=
  ∀ fs : Family, 0 < dimension fs →
    let raw := encodeFamily fs
    let C := bound raw
    cutoff B fs (names raw) ≤ C ∧
    high (C,raw) = (typedHigh fs).map encodeFamily ∧
    (∀ ch ∈ typedHigh fs, dimension ch < dimension fs) ∧
    ((∃ ρ : Nat → Nat, AllPaid C fs ρ ∧ Holds f ρ fs) ↔
      ∃ ch ∈ typedHigh fs, Satisfiable f ch)

noncomputable def next (f : Nat → Nat) (bound : BoundProgram) (typedHigh : TypedHigh)
    (fs : Family) : List Family :=
  if dimension fs = 0 then [] else
    low f (bound (encodeFamily fs)) fs (names (encodeFamily fs)) ++ typedHigh fs

def ExactSemanticDriverStep : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (bound : BoundProgram) (high : HighProgram) (typedHigh : TypedHigh),
    Certified f B bound high typedHigh → ∀ fs : Family,
      (ActualBitFamilyRawDriver.nextCode f bound high (encodeFamily fs) =
        (next f bound typedHigh fs).map encodeFamily) ∧
      (∀ ch ∈ next f bound typedHigh fs, dimension ch < dimension fs) ∧
      (0 < dimension fs → (Satisfiable f fs ↔ ∃ ch ∈ next f bound typedHigh fs, Satisfiable f ch))

def ExactSemanticDriverSolve : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (bound : BoundProgram) (high : HighProgram) (typedHigh : TypedHigh),
    Certified f B bound high typedHigh →
      ∀ fs : Family, solve f bound high (encodeFamily fs) = true ↔ Satisfiable f fs

def FullActualBitFamilyRawSemanticDriver : Prop :=
  ExactSemanticDriverStep ∧ ExactSemanticDriverSolve

end LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
