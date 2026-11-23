import LogicLineages.PersistentMarking.NativeTowerWitnessFamilyProof
import LogicLineages.PersistentMarking.NativeSyntaxCountabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowDomain

namespace LogicLineages.PersistentMarking.NativeTowerNumericCodeTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeTowerExtractorTargets
open NativeTowerExtractorGeneralTargets NativeTowerWitnessPrefixTargets
open NativeTowerWitnessFamilyTargets NativeTowerWitnessFamilyProof
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticPair (pair)
open NativeSyntaxCountabilityTargets

/-- One original ordinary application head and its two ordered base
arguments, never the numerical auxiliary-application constructor. -/
def appNode (σ τ : Ty) (f a : NTerm) : NTerm :=
  .ordinary (.app σ τ) (.cons f (.cons a .nil))

def appCode (σ τ : Ty) (f a : Nat) : Nat :=
  encodeNode 4 [encodeHead (.app σ τ),pair f (pair a 0 + 1) + 1]

def rawCode (q : Expr) : Nat := ((tr q).map encodeTerm).getD 0

def lowerCode : Nat → Nat → Nat
  | 0, head => head
  | l+1, head => lowerCode l (appCode (ty (l+2)) (ty (l+2)) head (rawCode (extractor l)))

def zeroCode : Nat := appCode indexType indexType (rawCode nativeNB) (rawCode omegaCarrier)

def towerCode : Nat → Nat
  | 0 => zeroCode
  | 1 => appCode indexType indexType (rawCode nativeNB) zeroCode
  | l+2 => appCode indexType indexType
      (appCode endo endo (lowerCode l (rawCode (extractor l))) (rawCode nativeNB)) zeroCode

def finalHead : Nat → Expr
  | 0 => nativeNB
  | 1 => nativeNB
  | l+2 => app endo endo (printedLower l (extractor l)) nativeNB

def ReadAt (q : Expr) (c : Nat) : Prop := ∃ Q : NTerm, tr q = some Q ∧ encodeTerm Q = c

def ExactPrintedTowerCodeRead : Prop :=
  ∀ (S : Signature) (n : Nat), ∃ F A : NTerm,
    let Q := appNode indexType indexType F A
    tr (finalHead n) = some F ∧
    tr (finalOperand n) = some A ∧
    tr (towerTerm n) = some Q ∧
    encodeTerm Q = towerCode n ∧
    decodeTerm (towerCode n) = some Q ∧
    NumberedWindowDomain.Typed EmptyContext Q indexType ∧
    nativeCode (closedTower S n) = towerCode n ∧
    0 < towerCode n

end LogicLineages.PersistentMarking.NativeTowerNumericCodeTargets
