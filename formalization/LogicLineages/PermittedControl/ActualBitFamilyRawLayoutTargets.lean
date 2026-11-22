module
public import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesTargets
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionCodeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLayout
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalMatrixLowDimensionCode (rawSupport)
open OriginalMatrixDenseRanks (support)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (originalRows wantedBits coordinates dimension)

abbrev RawBitRow := RawRow × Bool
abbrev RawFamily := List (List RawBitRow)

def encodeBitRow (r : BitRow) : RawBitRow := (encodeRow r.1,r.2)
def encodeFamily (family : Family) : RawFamily := family.map (List.map encodeBitRow)

def occurrences (family : RawFamily) : List Nat :=
  rawSupport (family.flatMap (List.map Prod.fst))

def appears (names : List Nat) (k : Nat) : Bool :=
  names.foldr (fun n seen => decide (n = k) || seen) false

def namesFrom (names : List Nat) : List Nat :=
  (List.range ((names.foldr max 0) + 1)).filterMap
    (fun k => if appears names k then some k else none)

/-- Sorted namespace on actual literal operands, not on the nonzero
coefficient support and not the opaque order of a Finset enumeration. -/
def names (family : RawFamily) : List Nat := namesFrom (occurrences family)

def ExactRawFamilyLayout : Prop :=
  ∀ family : Family,
    (encodeFamily family).map (List.map Prod.fst) = family.map (fun c => (originalRows c).map encodeRow) ∧
    (encodeFamily family).map (List.map Prod.snd) = family.map wantedBits ∧
    occurrences (encodeFamily family) = support (family.flatMap originalRows)

def ExactRawFamilyNames : Prop :=
  (∀ raw : RawFamily, (names raw).Pairwise (· < ·) ∧ (names raw).Nodup ∧
    ∀ k : Nat, k ∈ names raw ↔ k ∈ occurrences raw) ∧
  ∀ family : Family,
    (names (encodeFamily family)).toFinset = coordinates family ∧
    (names (encodeFamily family)).length = dimension family

def ExactRawLayoutEffectivity : Prop := Primrec occurrences ∧ Primrec names
def FullActualBitFamilyRawLayout : Prop :=
  ExactRawFamilyLayout ∧ ExactRawFamilyNames ∧ ExactRawLayoutEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawLayout
