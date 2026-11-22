module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNaturalFieldGates
open OrdinalComparison FieldComparison

abbrev Valuation := Nat → Nat

/-- The identity convention is explicit and is not a purported successful
read of an invalid equal-endpoint proper interval. -/
inductive Interval where
  | proper (lam mu : NONote)
  | identity (mu : NONote)

def IdentityDomain (mu : NONote) (x : Nat) : Prop :=
  (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) ∧ actualOrdinalNorm mu.1.repr ≤ x

def Interval.domain (x : Nat) : Interval → Prop
  | .proper lam mu => ClosedOrdinaryValueDomain (.entry 0 lam mu) x
  | .identity mu => IdentityDomain mu x

def Interval.left : Interval → NONote
  | .proper lam _ => lam
  | .identity mu => mu

def Interval.right : Interval → NONote
  | .proper _ mu | .identity mu => mu

def Interval.firstHit (f : Nat → Nat) (x i : Nat) (P : Interval) : Prop :=
  FirstEntry f (countInitial P.left.1.repr x) P.right.1.repr i

def Interval.entryNorm (f : Nat → Nat) (x i : Nat) (P : Interval) : Nat :=
  entryNormAt f (countInitial P.left.1.repr x) i

inductive Gate where
  | iterate (steps source output : Nat)
  | entry (P : Interval) (source output : Nat)
  | count (P : Interval) (source output : Nat)

def Gate.source : Gate → Nat
  | .iterate _ s _ | .entry _ s _ | .count _ s _ => s

def Gate.output : Gate → Nat
  | .iterate _ _ o | .entry _ _ o | .count _ _ o => o

def Gate.references (g : Gate) : List Nat := [g.source]

def Gate.domain (g : Gate) (x : Nat) : Prop :=
  match g with
  | .iterate .. => True
  | .entry P .. | .count P .. => P.domain x

def Gate.value (f : Nat → Nat) (x v : Nat) : Gate → Prop
  | .iterate steps _ _ => v = f^[steps] x
  | .entry P _ _ => ∃ i : Nat, P.firstHit f x i ∧ v = P.entryNorm f x i
  | .count P _ _ => P.firstHit f x v

noncomputable def identityRead (mu : NONote) (x v : Nat) : ClosedNaturalFieldResult :=
  @ite ClosedNaturalFieldResult (IdentityDomain mu x) (Classical.propDecidable _) (some (some v)) none

/-- Invalid, genuine miss, and genuine numeric hit are separate statuses. -/
noncomputable def Gate.readAt (f : Nat → Nat) (x : Nat) : Gate → ClosedNaturalFieldResult
  | .iterate steps _ _ => closedOrdinaryValueField f (longFieldCode (.iterate steps)) x
  | .entry (.proper lam mu) _ _ => closedOrdinaryValueField f (longFieldCode (.entry 0 lam mu)) x
  | .count (.proper lam mu) _ _ =>
      closedOrdinaryCountField f (rawNoteEncode lam.1,rawNoteEncode mu.1,x)
  | .entry (.identity mu) _ _ => identityRead mu x x
  | .count (.identity mu) _ _ => identityRead mu x 0

noncomputable def Gate.read (f : Nat → Nat) (g : Gate) (θ : Valuation) : ClosedNaturalFieldResult :=
  g.readAt f (θ g.source)

def Gate.graph (f : Nat → Nat) (g : Gate) (θ : Valuation) : Prop :=
  g.domain (θ g.source) ∧ g.value f (θ g.source) (θ g.output)

def ThreeWay (R : ClosedNaturalFieldResult) (domain : Prop) (value : Nat → Prop) : Prop :=
  (R = none ↔ ¬domain) ∧
  (R = some none ↔ domain ∧ ∀ v, ¬value v) ∧
  ∀ v, R = some (some v) ↔ domain ∧ value v

def ExactOrdinaryGateReads : Prop :=
  ∀ (f : Nat → Nat) (g : Gate) (x : Nat), ThreeWay (g.readAt f x) (g.domain x) (fun v => g.value f x v)

def ExactOrdinarySharedGateGraph : Prop :=
  ∀ (f : Nat → Nat) (g : Gate) (ν θ : Valuation),
    (g.read f θ = some (some (θ g.output)) ↔ g.graph f θ) ∧
    ((∀ n ∈ g.references, θ n = ν n) →
      g.read f θ = g.read f ν ∧ (θ g.output = ν g.output → (g.graph f θ ↔ g.graph f ν)))

def ExactOrdinaryIdentityBoundary : Prop :=
  ∀ (f : Nat → Nat) (mu : NONote) (x : Nat), IdentityDomain mu x →
    (Interval.identity mu).firstHit f x 0 ∧ (Interval.identity mu).entryNorm f x 0 = x ∧
    ∀ (s o : Nat), (Gate.entry (.identity mu) s o).readAt f x = some (some x) ∧
      (Gate.count (.identity mu) s o).readAt f x = some (some 0)

def FullOriginalNaturalFieldGates : Prop :=
  ExactOrdinaryGateReads ∧ ExactOrdinarySharedGateGraph ∧ ExactOrdinaryIdentityBoundary

end LogicLineages.PermittedControl.OriginalNaturalFieldGates
