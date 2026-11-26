module
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Genuine first hit of the target interval along actual nonfinite descent.
No value is invented if a small input skips a positive target. -/
def FirstEntry (f : Nat → Nat) (a nu : Ordinal.{0}) (i : Nat) : Prop :=
  nu ≤ (descentWith f)^[i] a ∧ (descentWith f)^[i] a < nu + Ordinal.omega0 ∧
  ∀ j : Nat, j < i → ¬ (nu ≤ (descentWith f)^[j] a ∧ (descentWith f)^[j] a < nu + Ordinal.omega0)

noncomputable def entryNormAt (f : Nat → Nat) (a : Ordinal.{0}) (i : Nat) : Nat :=
  actualOrdinalNorm ((descentWith f)^[i] a)

/-- Inputs are (initial normal code, target normal limit-part code). Search
for exact equality of the current limit part; a skipped target stays undefined. -/
def entrySearchWith (f : Nat → Nat) (p : Nat × Nat) : Part Nat :=
  Nat.rfind (fun i => Part.some (decide ((rawSplitCode (encodedStatesWith f p.1 i)).unpair.1 = p.2)))

def entryPartialWith (f : Nat → Nat) (p : Nat × Nat) : Part (Nat × Nat) :=
  (entrySearchWith f p).map (fun i => (rawNormCode (encodedStatesWith f p.1 i), i))

end LogicLineages.PermittedControl
