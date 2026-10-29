module
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section

/-! Exact finite-code norm algorithm and independent computation obligations.
The source norm is the full multiplicity additive tree norm. This stage is
only for raw ONote codes; it claims no normality, comparison, finite norm-ball
enumeration or collapse-evaluator effectiveness.
-/

namespace LogicLineages.OrdinalComparison.Targets

def RawNormTableEquation : Prop :=
  rawNormTable 0 = [0] ∧ ∀ n : Nat,
    rawNormTable (n + 1) = rawNormTable n ++
      [(n.unpair.2.unpair.1 + 1) * (1 + (rawNormTable n).getD n.unpair.1 0) +
        (rawNormTable n).getD n.unpair.2.unpair.2 0]

def RawNormCodeEquation : Prop :=
  rawNormCode 0 = 0 ∧ ∀ n : Nat,
    rawNormCode (n + 1) =
      (n.unpair.2.unpair.1 + 1) * (1 + rawNormCode n.unpair.1) +
        rawNormCode n.unpair.2.unpair.2

def RawNormCodeCorrect : Prop :=
  ∀ a : ONote, rawNormCode (rawNoteEncode a) = Vendor.R1.treeWeight a

def RawNormCodePrimitiveRecursive : Prop := Nat.Primrec rawNormCode

end LogicLineages.OrdinalComparison.Targets
