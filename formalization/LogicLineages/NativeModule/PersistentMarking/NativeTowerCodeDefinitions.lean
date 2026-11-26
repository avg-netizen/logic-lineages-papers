module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSequenceTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeSyntaxCountabilityTargets
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeTowerCode
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeTowerSequenceTargets
open NumberedWindowOrdinaryTranslation NumberedWindowArithmeticTermCode

/-- The existing ordinary translation followed by its existing numerical code.
No new encoding of native expressions is introduced. -/
def literalCode (q : Expr) : Option Nat := (tr q).map encodeTerm

/-- Used only for the three fixed closed native constants below. Their successful
translation is proved in the calibration; zero is the existing fallback. -/
def fixedCode (q : Expr) : Nat := (literalCode q).getD 0

abbrev pairCode := NumberedWindowArithmeticPair.pair

def consCode (a b : Nat) : Nat := pairCode a b + 1
def node2Code (tag a b : Nat) : Nat := consCode tag (consCode a (consCode b 0))
def arrowCode (a b : Nat) : Nat := consCode a b
def boundCode (a i : Nat) : Nat := node2Code 1 a i
def lamCode (a q : Nat) : Nat := node2Code 2 a q
def headCode (h args : Nat) : Nat := node2Code 4 h args
def appCode (a b f x : Nat) : Nat :=
  headCode (pairCode 4 (pairCode a b)) (consCode f (consCode x 0))

def indexCode : Nat := arrowCode 0 0
def zeroCode : Nat := headCode (pairCode 0 0) 0
def towerZeroCode : Nat := lamCode 0 (boundCode 0 0)
def stepTypeCode (a : Nat) : Nat := arrowCode 0 (arrowCode a a)
def recCode (a u step base : Nat) : Nat :=
  appCode a a
    (appCode (stepTypeCode a) (arrowCode a a)
      (appCode 0 (arrowCode (stepTypeCode a) (arrowCode a a))
        (headCode (pairCode 3 a) 0) u) step) base
def discardCode (a : Nat) : Nat := lamCode a (lamCode a (boundCode a 1))
def leftCode (a p : Nat) : Nat := appCode a (arrowCode a a) (discardCode a) p

/-- Literal codes of the actual types |A_l|, not of semantic ordinals. -/
def tierTypeCode : Nat → Nat := Nat.rec indexCode (fun _ a => arrowCode a a)

/-- Wrap the first `k` tier binders, with a fixed tier offset. -/
def wrapCode (offset k body : Nat) : Nat :=
  Nat.rec body (fun j out => lamCode (tierTypeCode (j + offset)) out) k

def bindersCode (k body : Nat) : Nat := wrapCode 1 k body

/-- The erased index is shifted once under each of the `l` new lambdas. -/
def eraseTierCode (l i : Nat) : Nat :=
  wrapCode 0 l (boundCode indexCode (i + l))

def iteratorCode (l : Nat) : Nat :=
  let b := tierTypeCode l
  let eta := arrowCode b b
  lamCode indexCode (lamCode eta (lamCode b
    (recCode b zeroCode
      (lamCode 0 (appCode eta eta (leftCode eta (boundCode eta 2)) (eraseTierCode (l+1) 3)))
      (boundCode b 0))))

def appliedCode (l i p u : Nat) : Nat :=
  let b := tierTypeCode l
  let eta := arrowCode b b
  appCode b b (appCode eta eta
    (appCode indexCode (arrowCode eta eta) (iteratorCode l) i) p) u

def slotCode (j : Nat) : Nat := boundCode (tierTypeCode j) j

/-- One descending application step in the literal (B_T) spine. -/
def natDownStep (state : Nat × Nat) : Nat × Nat :=
  (state.1 - 1, appCode (tierTypeCode state.1) (tierTypeCode state.1) state.2 (slotCode state.1))

def natDownCode (m v : Nat) : Nat :=
  appCode indexCode indexCode ((natDownStep^[m]) (m,v)).2 towerZeroCode

def spineCode : Nat → Nat
  | 0 => appliedCode 0 (boundCode indexCode 0) (slotCode 1) towerZeroCode
  | m+1 => natDownCode m
      (appliedCode (m+1) (boundCode indexCode 0) (slotCode (m+2)) (slotCode (m+1)))

def towerCode (l : Nat) : Nat :=
  bindersCode (l+1)
    (appCode (tierTypeCode 1) (tierTypeCode 1)
      (fixedCode NativeOrdinalExponentialTargets.ordinalFix) (lamCode indexCode (spineCode l)))

def veblenCode : Nat :=
  appCode (tierTypeCode 1) (tierTypeCode 1)
    (appCode (tierTypeCode 2) (tierTypeCode 2) (towerCode 1) (towerCode 0))
    (fixedCode NativeOrdinalExponentialTargets.ordinalNext)

def baseCode : Nat :=
  appCode indexCode indexCode veblenCode (fixedCode NativeOrdinalBasisTargets.omegaCarrier)

/-- One descending application step in the literal (D) spine. -/
def downStep (state : Nat × Nat) : Nat × Nat :=
  (state.1 - 1, appCode (tierTypeCode (state.1+1)) (tierTypeCode (state.1+1))
    state.2 (towerCode (state.1-1)))

def downCode (k v : Nat) : Nat := ((downStep^[k]) (k,v)).2

/-- Actual numerical codes of the explicit native tower family of (D).
Every operation is arithmetic, a fixed constant, or bounded iteration. -/
def sequenceCode : Nat → Nat
  | 0 => baseCode
  | 1 => appCode indexCode indexCode veblenCode baseCode
  | l+2 => appCode indexCode indexCode
      (appCode (tierTypeCode 1) (tierTypeCode 1) (downCode l (towerCode l)) veblenCode) baseCode

end LogicLineages.PersistentMarking.NativeTowerCode
