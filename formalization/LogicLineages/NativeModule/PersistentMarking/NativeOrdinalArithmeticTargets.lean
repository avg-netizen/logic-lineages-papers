module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalBasisTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeIteratorTargets NativeOrdinalBasisTargets

abbrev endo : Ty := .arrow indexType indexType
abbrev binaryType : Ty := .arrow indexType endo

def binaryApplication (operation a b : Expr) : Expr :=
  app indexType indexType (app indexType endo operation a) b

def additionBody : Expr :=
  .lam indexType (applied .base (.bound indexType 0) ordinalSuccessor (.bound indexType 1))

def addition : Expr := .lam indexType additionBody

def multiplicationBody : Expr :=
  .lam indexType (applied .base (.bound indexType 0)
    (.lam indexType (binaryApplication addition (.bound indexType 0) (.bound indexType 2))) ordinalZero)

def multiplication : Expr := .lam indexType multiplicationBody

def additionAfterFirst (a : Expr) : Expr :=
  applied .base (.bound indexType 0) ordinalSuccessor a

def multiplicationStep (a : Expr) : Expr :=
  .lam indexType (binaryApplication addition (.bound indexType 0) a)

def multiplicationAfterFirst (a : Expr) : Expr :=
  applied .base (.bound indexType 0) (multiplicationStep a) ordinalZero

def additionResult (a b : Expr) : Expr := applied .base b ordinalSuccessor a

def multiplicationResult (a b : Expr) : Expr := applied .base b (multiplicationStep a) ordinalZero

def ClosedOrdinalAdditionMultiplication : Prop :=
  ∀ S, ClosedNative S addition binaryType ∧ ClosedNative S multiplication binaryType

def BinaryOrdinalBeta (operation : Expr) (afterFirst : Expr → Expr) (result : Expr → Expr → Expr) : Prop :=
  ∀ S (a b : ClosedNativeTerm S indexType),
    ∃ start mid final : ClosedNativeTerm S indexType,
      start.val = binaryApplication operation a.val b.val ∧
      mid.val = app indexType indexType (.lam indexType (afterFirst a.val)) b.val ∧
      final.val = result a.val b.val ∧
      Reduction S start.val mid.val ∧ Reduction S mid.val final.val ∧
      NativeBelow mid start ∧ NativeBelow final mid

def OrdinalAdditionBeta : Prop := BinaryOrdinalBeta addition additionAfterFirst additionResult

def OrdinalMultiplicationBeta : Prop :=
  BinaryOrdinalBeta multiplication multiplicationAfterFirst multiplicationResult

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticTargets
