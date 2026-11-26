module
public import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingTargets
public import LogicLineages.PermittedControl.ActualInitialSignedCountCleanupTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedCleanup
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualEffectiveTerminalSignBound (shortLengthCode)
open ActualShortCountCleanup (shortLength)
open ActualSymbolicZeroSuccessor (SyntaxState cleanSyntax cleanupShift)
open ActualInitialSignedCountCleanup (cleanup)

def retainCode (terms : List WeightedCode) : List WeightedCode :=
  terms.filter (fun t => decide (shortLengthCode t.2 = 0))

def shiftCode (terms : List WeightedCode) : Int :=
  terms.foldr (fun t rest => t.1 * (shortLengthCode t.2 : Int) + rest) 0

def cleanupCode (s : RawSyntax) : RawSyntax := (s.1 + shiftCode s.2,retainCode s.2)

def ExactRawInitialCleanup : Prop :=
  (∀ op : LowerOperand, shortLengthCode op.code = shortLength op) ∧
  (∀ terms : List WeightedOperand,
    retainCode (terms.map encodeWeighted) = (cleanSyntax terms).map encodeWeighted) ∧
  (∀ terms : List WeightedOperand, shiftCode (terms.map encodeWeighted) = cleanupShift terms) ∧
  ∀ s : SyntaxState, cleanupCode (encodeSyntax s) = encodeSyntax (cleanup s)

def ExactRawInitialCleanupEffectivity : Prop :=
  Primrec shortLengthCode ∧ Primrec retainCode ∧ Primrec shiftCode ∧ Primrec cleanupCode

def FullActualRawSignedCleanup : Prop := ExactRawInitialCleanup ∧ ExactRawInitialCleanupEffectivity

end LogicLineages.PermittedControl.ActualRawSignedCleanup
