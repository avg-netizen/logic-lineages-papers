module
public import LogicLineages.PermittedControl.ActualBitFamilyRawClosedTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawLowTargets
public import LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStepTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawDriver
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (RawFamily encodeFamily names)
open ActualBitFamilyRawClosed (closedCode)
open ActualBitFamilyRawLow (stripsCode)
open ActualBitFamilyExistentialLow (closed Satisfiable)
open ActualBitFamilyLowSlices (dimension)
open ActualNamedBitFamilyHigh (cutoff)
open ActualNamedBitFamilyCommonCutoffStep (low children)

abbrev BoundProgram := RawFamily → Nat
abbrev HighProgram := Nat × RawFamily → List RawFamily
abbrev State := Bool × List RawFamily
abbrev TypedState := Bool × List Family

/-- The supplied compiler emits the exact ordered encoded high children at the
same sufficient bound used for the raw low enumeration. This is a hypothesis,
not an implementation of that compiler or a decidability assumption. -/
def Calibrated (B : Nat) (bound : BoundProgram) (high : HighProgram) : Prop :=
  ∀ fs : Family, 0 < dimension fs →
    let raw := encodeFamily fs
    let C := bound raw
    cutoff B fs (names raw) ≤ C ∧
    high (C,raw) = ((ActualNamedBitFamilyHighAbove.compile C fs (names raw)).map Prod.snd).map encodeFamily

def depth (raw : RawFamily) : Nat := (names raw).length

noncomputable def lowCode (f : Nat → Nat) (C : Nat) (raw : RawFamily) : List RawFamily :=
  (names raw).flatMap (fun k => (stripsCode f (k,C,raw)).map Prod.snd)

def hit (raw : RawFamily) : Bool := decide (depth raw = 0) && closedCode raw

noncomputable def nextCode (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (raw : RawFamily) : List RawFamily :=
  if depth raw = 0 then [] else
    let C := bound raw
    lowCode f C raw ++ high (C,raw)

noncomputable def advance (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram) (s : State) : State :=
  (s.1 || s.2.any hit,s.2.flatMap (nextCode f bound high))

noncomputable def scan (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (s : State) (n : Nat) : State :=
  Nat.rec s (fun _ t => advance f bound high t) n

noncomputable def solve (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram) (raw : RawFamily) : Bool :=
  (scan f bound high (false,[raw]) (depth raw + 1)).1

def typedHit (fs : Family) : Bool := decide (dimension fs = 0) && closed fs

noncomputable def typedNext (f : Nat → Nat) (bound : BoundProgram) (fs : Family) : List Family :=
  if dimension fs = 0 then [] else children f (bound (encodeFamily fs)) fs (names (encodeFamily fs))

noncomputable def typedAdvance (f : Nat → Nat) (bound : BoundProgram) (s : TypedState) : TypedState :=
  (s.1 || s.2.any typedHit,s.2.flatMap (typedNext f bound))

noncomputable def typedScan (f : Nat → Nat) (bound : BoundProgram) (s : TypedState) (n : Nat) : TypedState :=
  Nat.rec s (fun _ t => typedAdvance f bound t) n

def encodeState (s : TypedState) : State := (s.1,s.2.map encodeFamily)

def Witness (f : Nat → Nat) (s : TypedState) : Prop :=
  s.1 = true ∨ ∃ fs ∈ s.2, Satisfiable f fs

def ExactDriverTransport : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (bound : BoundProgram) (high : HighProgram),
    Calibrated B bound high → ∀ (s : TypedState) (n : Nat),
      scan f bound high (encodeState s) n = encodeState (typedScan f bound s n)

def ExactDriverDepth : Prop :=
  ∀ (f : Nat → Nat) (bound : BoundProgram) (s : TypedState) (limit : Nat),
    (∀ fs ∈ s.2, dimension fs ≤ limit) →
    ∀ n : Nat, ∀ fs ∈ (typedScan f bound s n).2, dimension fs + n ≤ limit

def ExactDriverSolve : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (bound : BoundProgram) (high : HighProgram),
    SelectedWithThreshold f B → Calibrated B bound high →
      ∀ fs : Family, (solve f bound high (encodeFamily fs) = true ↔ Satisfiable f fs)

def ExactDriverEffectivity : Prop :=
  ∀ (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram),
    Computable f → Computable bound → Computable high → Computable (solve f bound high)

def FullActualBitFamilyRawDriver : Prop :=
  ExactDriverTransport ∧ ExactDriverDepth ∧ ExactDriverSolve ∧ ExactDriverEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawDriver
