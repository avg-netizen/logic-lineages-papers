module
public import LogicLineages.OrdinalComparison.OptimizedMaximumDefinitions
public import LogicLineages.OrdinalComparison.EncodedMaximumDefinitions
public import LogicLineages.OrdinalComparison.EncodedNaturalSumDefinitions
public import LogicLineages.OrdinalComparison.RawNormalDefinitions

@[expose] public section

/-! Literal implementation of paper05 thm:maximum. Both source queries use
one structurally recursive fuel interpreter. The fuel is a proved rank bound,
not a search cutoff in the public wrapper; correctness for every larger fuel
and its agreement with the independent exhaustive maximum are separate targets.
No exhaustive maximum is called by this optimized interpreter. -/

namespace LogicLineages.OrdinalComparison

def optimizedRawBlock (e : ONote) (c : Nat) (r : ONote) : ONote :=
  if hc : c = 0 then r else ONote.oadd e ⟨c, Nat.pos_of_ne_zero hc⟩ r

/-- `true` is source M; `false` is source L. -/
def optimizedRawMaximumFuel : Nat → ONote → Nat → Bool → ONote
  | 0, _, _, _ => 0
  | fuel + 1, n, b, true =>
      if b = 0 then 0 else
      match n with
      | .zero => 0
      | .oadd e c r =>
          let w := 1 + Vendor.R1.treeWeight e
          if r ≠ 0 ∧ (c : Nat) * w ≤ b then
            ONote.oadd e c (optimizedRawMaximumFuel fuel r (b - (c : Nat) * w) true)
          else
            let d := min (if r = 0 then (c : Nat) - 1 else (c : Nat)) (b / w)
            optimizedRawBlock e d (optimizedRawMaximumFuel fuel e (b - d * w) false)
  | fuel + 1, e, b, false =>
      if b = 0 ∨ e = 0 then 0 else
      let a := optimizedRawMaximumFuel fuel e (b - 1) true
      let v := 1 + Vendor.R1.treeWeight a
      let q := b / v
      let s := b % v
      optimizedRawBlock a q (optimizedRawMaximumFuel fuel a s false)

/-- Public numerical M implementation, with explicit rejection of nonnormal codes. -/
def encodedOptimizedMaximum (n b : Nat) : Nat :=
  if rawNormalCode n = 1 ∧ n ≠ 0 then
    rawNoteEncode (optimizedRawMaximumFuel (optimizedMaximumRank b 1 + 1)
      (rawNoteDecode n) b true)
  else 0

/-- Public numerical L implementation, including exponent zero. -/
def encodedOptimizedLowerPower (n b : Nat) : Nat :=
  if rawNormalCode n = 1 then
    rawNoteEncode (optimizedRawMaximumFuel (optimizedMaximumRank b 0 + 1)
      (rawNoteDecode n) b false)
  else 0

end LogicLineages.OrdinalComparison
