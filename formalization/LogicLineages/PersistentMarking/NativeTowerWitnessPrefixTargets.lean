import LogicLineages.PersistentMarking.NativeTowerExtractorTargets

namespace LogicLineages.PersistentMarking.NativeTowerWitnessPrefixTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeCarrierTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeTowerExtractorTargets

/-- The printed finite-type ladder A₀=ι, Aₖ₊₁=Aₖ→Aₖ, interpreted
by the original native-type translation, not by a new type universe. -/
def level : Nat → SemanticType
  | 0 => .base
  | n+1 => .arrow (level n) (level n)

abbrev ty (n : Nat) : Ty := actualType (level n)

/-- Literal original Expr codes of one finite prefix B₀,…,B_l, in
ascending storage order. This raw type makes no validity claims. -/
inductive RawPrefix : Nat → Type where
  | first : Expr → RawPrefix 0
  | extend {n : Nat} : RawPrefix n → Expr → RawPrefix (n+1)

def RawPrefix.top : RawPrefix n → Expr
  | .first q => q
  | .extend _ q => q

/-- If the original current head is at A_(l+2), apply the remaining
extractors from B_(l−1) down to B₀, left associatively. -/
def RawPrefix.lower : {n : Nat} → RawPrefix n → Expr → Expr
  | 0, .first _, q => q
  | n+1, .extend previous _, q =>
    lower previous (app (ty (n+2)) (ty (n+2)) q previous.top)

/-- Provided closed native extractor operands at the original types.
This does not assert that any supplied code is a literal printed B_l. -/
inductive ClosedPrefix (S : Signature) : Nat → Type where
  | first : ClosedNativeTerm S (ty 2) → ClosedPrefix S 0
  | extend {n : Nat} : ClosedPrefix S n → ClosedNativeTerm S (ty (n+3)) → ClosedPrefix S (n+1)

def ClosedPrefix.raw : ClosedPrefix S n → RawPrefix n
  | .first q => .first q.val
  | .extend previous q => .extend previous.raw q.val

def ClosedPrefix.top : ClosedPrefix S n → ClosedNativeTerm S (ty (n+2))
  | .first q => q
  | .extend _ q => q

/-- Printed Δ₀ and Δ₁ with the literal native operands. -/
def t0 : Expr := app indexType indexType nativeNB omegaCarrier
def t1 : Expr := app indexType indexType nativeNB t0

/-- The term for printed Δ_(l+2), given the genuine literal B-prefix. -/
def later (p : RawPrefix n) : Expr :=
  app indexType indexType (app endo endo (p.lower p.top) nativeNB) t0

def p0 : RawPrefix 0 := .first extractorZero
def p1 : RawPrefix 1 := .extend p0 extractorOne
def t2 : Expr := later p0
def t3 : Expr := later p1

def ExactFirstFourTowerWitnesses : Prop :=
  (t0 = app indexType indexType nativeNB omegaCarrier) ∧
  (t1 = app indexType indexType nativeNB t0) ∧
  (t2 = app indexType indexType (app endo endo extractorZero nativeNB) t0) ∧
  (t3 = app indexType indexType
    (app endo endo (app levelTwo levelTwo extractorOne extractorZero) nativeNB) t0) ∧
  ∀ S, ClosedNative S t0 indexType ∧ ClosedNative S t1 indexType ∧
    ClosedNative S t2 indexType ∧ ClosedNative S t3 indexType

/-- Only actual argument selection, not an ordinal interpretation of
these terms and not a chain between all four members. -/
def ExactFirstFourTowerArgumentEdges : Prop :=
  ∀ S, ConfinedPair.Strict S t0 omegaCarrier ∧ ConfinedPair.Strict S t1 t0 ∧
    ConfinedPair.Strict S t2 t0 ∧ ConfinedPair.Strict S t3 t0

end LogicLineages.PersistentMarking.NativeTowerWitnessPrefixTargets
