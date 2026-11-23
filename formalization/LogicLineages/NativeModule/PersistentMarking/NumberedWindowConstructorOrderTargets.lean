module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalMultisetClosureTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorOrderTargets
open Spine NumberedWindowDomain NumberedWindowArithmeticFields
open NumberedWindowExternalIDOperators NumberedWindowArithmeticDirectMultisetTargets

/-- The four parameters of (L). A missing finite label denotes the ordinary head at ω. -/
structure Measure where
  head : Head
  base : List Nat
  label : Option Nat
  extras : List Nat

def LabelBelow : Option Nat → Option Nat → Prop
  | some i, some j => i < j
  | some _, none => True
  | _, _ => False

def AdmittedMeasure (S : Signature) (K : List Ty) (m : Measure) : Prop :=
  HeadInWindow S K m.head ∧ Least (multisetStep S K) (encodeFields m.base) ∧
    Least (multisetStep S K) (encodeFields m.extras)

/-- An earlier coordinate allows arbitrary later parameters. An unchanged
base is identified up to the actual occurrence permutation. -/
def Earlier (S : Signature) (K : List Ty) (n m : Measure) : Prop :=
  Precedes S m.head n.head ∨ (Equivalent S m.head n.head ∧
    (AddressDirect S K m.base n.base ∨ (m.base.Perm n.base ∧
      (LabelBelow n.label m.label ∨ (m.label = n.label ∧ AddressDirect S K m.extras n.extras)))))

def AdmittedEarlier (S : Signature) (K : List Ty) (n m : Measure) : Prop :=
  AdmittedMeasure S K n ∧ Earlier S K n m

def ConstructorMeasureAccessible : Prop :=
  ∀ S K m, AdmittedMeasure S K m → Acc (AdmittedEarlier S K) m

/-- The predicate can quantify over any output type, position-specific
representatives, and extra argument list attached to these four parameters. -/
def ConstructorMeasureInduction : Prop :=
  ∀ S K (P : Measure → Prop),
    (∀ m, AdmittedMeasure S K m → (∀ n, AdmittedMeasure S K n → Earlier S K n m → P n) → P m) →
    ∀ m, AdmittedMeasure S K m → P m

end LogicLineages.PersistentMarking.NumberedWindowConstructorOrderTargets
