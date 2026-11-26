import LogicLineages.PersistentMarking.NativeClosedApplication

namespace LogicLineages.PersistentMarking.NativeOrdinalBasisTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeClosedApplication

def ordinalZero : Expr := .lam .ground (.bound .ground 0)
def ordinalSuccessorBody : Expr := app indexType indexType (left indexType ordinalZero) (.bound indexType 0)
def ordinalSuccessor : Expr := .lam indexType ordinalSuccessorBody
def successorInstance (a : Expr) : Expr := app indexType indexType (left indexType ordinalZero) a
def omegaCarrier : Expr := W indexType ordinalSuccessor ordinalZero

def cap {S B} (P : ClosedNativeTerm S (.arrow B B)) (U : ClosedNativeTerm S B) : ClosedNativeTerm S B :=
  ⟨W B P.val U.val, NativeClosedProof.carrier S B P.val U.val P.property U.property⟩

def finiteApplication {S B} (P : ClosedNativeTerm S (.arrow B B)) (U : ClosedNativeTerm S B) :
    Nat → ClosedNativeTerm S B
  | 0 => U
  | n + 1 => applyClosed P (finiteApplication P U n)

def ClosedOrdinalBasis : Prop :=
  ∀ S, ClosedNative S ordinalZero indexType ∧
    ClosedNative S ordinalSuccessor (.arrow indexType indexType) ∧
    ClosedNative S omegaCarrier indexType

def OrdinalSuccessorSteps : Prop :=
  ∀ S (a : ClosedNativeTerm S indexType),
    ∃ start midpoint : ClosedNativeTerm S indexType,
      start.val = app indexType indexType ordinalSuccessor a.val ∧
      midpoint.val = successorInstance a.val ∧
      Reduction S start.val midpoint.val ∧ NativeBelow midpoint start ∧ NativeBelow a midpoint

def CapAboveFiniteApplications : Prop :=
  ∀ S B (P : ClosedNativeTerm S (.arrow B B)) (U : ClosedNativeTerm S B) n,
    (cap P U).val = recTerm B zero (.lam .ground P.val) U.val ∧
    NativeBelow (finiteApplication P U n) (cap P U)

end LogicLineages.PersistentMarking.NativeOrdinalBasisTargets
