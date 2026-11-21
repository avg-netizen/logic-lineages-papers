module
public import LogicLineages.PermittedControl.InnerTerminationTargets
public import LogicLineages.PermittedControl.FieldComparisonTargets
public import LogicLineages.PermittedControl.CountTransferTargets
public import LogicLineages.PermittedControl.FixedEntryClosedScanTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedCountOnlyClass
open OrdinalComparison FieldComparison InnerTerminationTargets

abbrev Interval := NONote × NONote
abbrev Occurrence (r : Nat) := Interval × Fin r
abbrev CountOnlyRow (r : Nat) := Row Empty Interval r

/-- Literal normal-form notation of omega squared: exponent two,
coefficient one, and zero remainder. -/
def omegaSquareNote : NONote :=
  ⟨ONote.oadd (ONote.ofNat 2) 1 ONote.zero, by decide⟩

def prefixTarget (μ : NONote) : NONote := μ + omegaSquareNote

/-- Literal original prefix scan at the same raw coordinate. It must
allow the identity prefix lambda=eta, so it is deliberately NOT sent
through the strict proper-interval ordinary field reader. -/
noncomputable def prefixRead {r : Nat} (f : Nat → Nat) (ρ : Fin r → Nat)
    (c : Occurrence r) : Option (Option (Nat × Nat)) :=
  fixedEntryClosedScan f
    (rawNoteEncode c.1.1.1, rawNoteEncode (prefixTarget c.1.2).1, ρ c.2)

/-- Neither an invalid scan nor a genuine miss is a numeric key. -/
noncomputable def fullKey {r : Nat} (f : Nat → Nat) (ρ : Fin r → Nat)
    (c : Occurrence r) : Option (Option Nat) :=
  (prefixRead f ρ c).map (fun v => v.map (fun p => f p.1))

noncomputable def members {r : Nat} (R : CountOnlyRow r) (f : Nat → Nat)
    (ρ : Fin r → Nat) (seed : Occurrence r) : Finset (Occurrence r) :=
  match fullKey f ρ seed with
  | some (some C) => R.count.support.filter (fun c => fullKey f ρ c = some (some C))
  | _ => ∅

def signedWeight {r : Nat} (R : CountOnlyRow r) (S : Finset (Occurrence r)) : Int :=
  ∑ c ∈ S, R.count c

/-- Test the selected class, never a caller-supplied eligibility witness.
There is no ordinary coefficient because the ordinary syntax is Empty. -/
noncomputable def zeroEligible {r : Nat} (R : CountOnlyRow r) (f : Nat → Nat)
    (ρ : Fin r → Nat) (seed : Occurrence r) : Bool := by
  classical
  let S := members R f ρ seed
  exact decide (S.Nonempty ∧ signedWeight R S = 0)

def PrefixNotationExact : Prop :=
  omegaSquareNote.1.repr = Ordinal.omega0 ^ (2 : Ordinal.{0}) ∧
  ∀ μ : NONote, (prefixTarget μ).1.repr = μ.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})

/-- CountCore's actual original and prefix entries and the exact doubled
integer annotation. The numerical key is paid by the literal prefix hit,
not postulated as an independent class oracle. -/
def ActualCoreRecord {r : Nat} (f : Nat → Nat) (ρ : Fin r → Nat)
    (c : Occurrence r) (i k q : Nat) : Prop :=
  let lam := c.1.1
  let mu := c.1.2
  let eta := prefixTarget mu
  let x := ρ c.2
  let A := countInitial lam.1.repr x
  eta.1.repr ≤ lam.1.repr ∧
  FirstEntry f A eta.1.repr i ∧ FirstEntry f A mu.1.repr k ∧
  q = entryNormAt f A i ∧ q = f^[i] x ∧
  prefixRead f ρ c = some (some (q,i)) ∧
  fullKey f ρ c = some (some (f q)) ∧
  2 * (k : Int) = (f q : Int) + 2 * (i : Int) + 2 * Targets.countCoreConstant mu.1.repr

/-- The seed designates an active original count occurrence, not a class
list, collision witness, key or eligibility result. The conclusion is
pointwise in one strictly ordered actual raw valuation. -/
def ActualClassExtraction : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (r : Nat) (R : CountOnlyRow r) (ρ : Fin r → Nat) (seed : Occurrence r),
    StrictMono ρ → seed ∈ R.count.support →
    (∀ c ∈ R.count.support,
      LongField (.entry 0 c.1.1 c.1.2) ∧
      max (actualOrdinalNorm c.1.1.1.repr) (actualOrdinalNorm c.1.2.1.repr + 3) ≤ ρ c.2) →
    let S := members R f ρ seed
    S ⊆ R.count.support ∧ seed ∈ S ∧
    (zeroEligible R f ρ seed = true ↔ (∑ c ∈ S, R.count c) = 0) ∧
    ∃ i₀ k₀ q₀ : Nat, ActualCoreRecord f ρ seed i₀ k₀ q₀ ∧
      ∀ c ∈ R.count.support, ∃ i k q : Nat,
        ActualCoreRecord f ρ c i k q ∧ (c ∈ S ↔ f q = f q₀)

/-- One actual count-only class and its signed zero test; no symbolic
branch generator, minimum, disposition, row replacement or charge claim. -/
def FullSelectedCountOnlyClass : Prop := PrefixNotationExact ∧ ActualClassExtraction

end LogicLineages.PermittedControl.SelectedCountOnlyClass
