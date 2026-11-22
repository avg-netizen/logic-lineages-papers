module
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowCoordinateSlice
open OrdinalComparison FieldComparison PreparedProjection FiniteStripCollectorRecovery
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted orderedReads actualSum)

abbrev Residual (A : Type) := Int × List (Int × A)
abbrev Result (A : Type) := Option (Option (Residual A))
abbrev RawArgs := Nat × Nat × Int × List WeightedCode

def encodeResidual (r : Residual LowerOperand) : Residual LowerOperandCode :=
  (r.1,r.2.map encodeWeighted)

/-- The original one-occurrence reader returns an empty hit when the rank
is untouched, and a singleton hit with the actual value at a selected rank. -/
def step {A : Type} (t : Int × A) (head : ReadResult) (tail : Result A) : Result A :=
  match head with
  | none => none
  | some none => some none
  | some (some hits) => tail.map (fun r => r.map (fun rest =>
      match hits.head? with
      | none => (rest.1,t :: rest.2)
      | some (_,v) => (rest.1 + t.1 * (v : Int),rest.2)))

noncomputable def sliceCode (f : Nat → Nat) (arg : RawArgs) : Result LowerOperandCode :=
  let (rank,a,c,terms) := arg
  terms.foldr (fun t tail => step t (readCode f rank a (1,t.2)) tail) (some (some (c,[])))

noncomputable def slice (f : Nat → Nat) (rank a : Nat) (c : Int)
    (terms : List WeightedOperand) : Result LowerOperand :=
  terms.foldr (fun t tail => step t (expectedRead f rank a (1,t.2)) tail) (some (some (c,[])))

def selected (rank : Nat) (terms : List WeightedOperand) : List WeightedOperand :=
  terms.filter (fun t => decide (t.2.rank = rank))

def untouched (rank : Nat) (terms : List WeightedOperand) : List WeightedOperand :=
  terms.filter (fun t => decide (t.2.rank ≠ rank))

def denotes (f ρ : Nat → Nat) (m : Nat) (c : Int) (terms : List WeightedOperand) : Prop :=
  ∃ values : List Nat, orderedReads f ρ terms values ∧ (m : Int) ∣ c + actualSum terms values

def sourceDomain (a : Nat) : LowerOperand → Prop
  | .coordinate _ => True
  | .ordinary _ F => ClosedOrdinaryValueDomain F a
  | .count _ lam mu => ClosedOrdinaryValueDomain (.entry 0 lam mu) a

inductive Failure where
  | invalid
  | genuineMiss

/-- The first selected failing occurrence remains visible. All earlier
selected occurrences must have genuine successful reads. -/
def firstFailure (f : Nat → Nat) (rank a : Nat) (terms : List WeightedOperand)
    (kind : Failure) : Prop :=
  ∃ (earlier : List WeightedOperand) (t : WeightedOperand) (later : List WeightedOperand),
    terms = earlier ++ (t :: later) ∧ t.2.rank = rank ∧
    (∀ u ∈ earlier, u.2.rank = rank → ∃ v, LowerOperandActual f (fun _ => a) u.2 v) ∧
    match kind with
    | .invalid => ¬ sourceDomain a t.2
    | .genuineMiss => sourceDomain a t.2 ∧ ∀ v, ¬ LowerOperandActual f (fun _ => a) t.2 v

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (sliceCode f)) ∧
  ∀ (f : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand),
    sliceCode f (rank,a,c,terms.map encodeWeighted) =
      (slice f rank a c terms).map (Option.map encodeResidual)

def FailureExact : Prop :=
  ∀ (f : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand),
    (slice f rank a c terms = none ↔ firstFailure f rank a terms .invalid) ∧
    (slice f rank a c terms = some none ↔ firstFailure f rank a terms .genuineMiss)

/-- One genuine slice of the unprepared signed row. Other raw coordinates
are arbitrary, and every original untouched term stays in its place. -/
def HitExact : Prop :=
  ∀ (f : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand)
      (b : Int) (rest : List WeightedOperand),
    slice f rank a c terms = some (some (b,rest)) →
    rest = untouched rank terms ∧
    ∀ ρ : Nat → Nat, ρ rank = a →
      ∃ values : List Nat, orderedReads f ρ (selected rank terms) values ∧
        b = c + actualSum (selected rank terms) values ∧
        ∀ m : Nat, 0 < m → (denotes f ρ m c terms ↔ denotes f ρ m b rest)

def FullSignedRowCoordinateSlice : Prop := CodeExact ∧ FailureExact ∧ HitExact

end LogicLineages.PermittedControl.SignedRowCoordinateSlice
