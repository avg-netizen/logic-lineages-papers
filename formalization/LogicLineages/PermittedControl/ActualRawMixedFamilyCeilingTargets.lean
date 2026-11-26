module
public import LogicLineages.PermittedControl.ActualRawSignedCleanupTargets
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted weightedTailCode)
open ActualRawSignedStaticCeiling (staticCode)
open ActualRawSignedCleanup (cleanupCode)
open ActualBitFamilyRawReadCeiling (rowCode)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open ActualGuardedResidualBitFamily (Family)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualGreatestCongruenceRoute (modulusMinimum)
open OriginalRankedLiteralClauseHigh (rowNeed clauseNeed familyNeed)

def rowBound (B r : Nat) (row : RawBitRow) : Nat :=
  let source := row.1
  let header := source.1
  let terms := source.2.2
  let internal :=
    if header.1 = 3 then weightedTailCode B header.2 terms
    else staticCode B r (cleanupCode source.2)
  max (rowCode source) internal

def clauseBound (B r : Nat) (rows : List RawBitRow) : Nat :=
  rows.foldr (fun row n => max (rowBound B r row) n) 0

/-- Cover even the clauses which the typed proper filter rejects.
This safe over-budget does not assert that any extra clause is valid. -/
def familyBound (B r : Nat) (family : RawFamily) : Nat :=
  family.foldr (fun rows n => max (clauseBound B r rows) n) 0

def ExactRawMixedRowMajorants : Prop :=
  (∀ (B m : Nat) (s : SyntaxState),
    weightedTailCode B m (s.terms.map encodeWeighted) = modulusMinimum B m s) ∧
  ∀ (B r : Nat) (row : BitRow), rowNeed B r row ≤ rowBound B r (encodeBitRow row)

def ExactRawMixedFamilyMajorants : Prop :=
  (∀ (B r : Nat) (rows : List BitRow),
    clauseNeed B r rows ≤ clauseBound B r (rows.map encodeBitRow)) ∧
  ∀ (B r : Nat) (family : Family),
    familyNeed B r family ≤ familyBound B r (encodeFamily family)

def ExactRawMixedFamilyCeilingEffectivity : Prop :=
  Primrec (fun p : Nat × Nat × RawBitRow => rowBound p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List RawBitRow => clauseBound p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × RawFamily => familyBound p.1 p.2.1 p.2.2)

def FullActualRawMixedFamilyCeiling : Prop :=
  ExactRawMixedRowMajorants ∧ ExactRawMixedFamilyMajorants ∧ ExactRawMixedFamilyCeilingEffectivity

end LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
