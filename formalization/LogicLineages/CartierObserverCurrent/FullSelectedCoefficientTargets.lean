module
public import LogicLineages.OrdinalComparison.BinaryObserverTargets

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullSelectedCoefficient.Targets
open LogicLineages.OrdinalComparison

/-- Literal e0, not an arbitrary initial state. -/
def InitialVector : Prop := ∀ D : Nat,
  actualBinaryCoefficientVector D (1 : Polynomial (ZMod 2)) = actualBinaryInitialVector D

/-- Exact noncommutative product order for least-significant-first bits. -/
def ProductOrder : Prop := ∀ D : Nat, ∀ A : Polynomial (ZMod 2),
  ∀ w : List Bool, ∀ v : Fin D → ZMod 2,
    actualBinaryMatrixWord D A w v =
      Matrix.mulVec ((w.reverse.map (actualBinaryTransitionMatrix D A)).prod) v

/-- Complete current thm:observer. Zero coordinate is the literal e0-transpose
output; parity is a Nat modulo2, not a confused field/count equality. -/
def SelectedCoefficient : Prop := ∀ d : Nat, ∀ hd : 0 < d,
  ∀ n : Nat, ∀ w : List Bool, actualBinaryWordValue w = n →
    (Matrix.mulVec
      ((w.reverse.map (actualBinaryTransitionMatrix (d * (d + 1) / 2)
        (actualBinarySourceDenominator d))).prod)
      (actualBinaryInitialVector (d * (d + 1) / 2))
      ⟨0, actualBinarySourceDimensionPositive d hd⟩).val = restrictedPartitionCount d n % 2

def CompleteSelectedCoefficient : Prop := InitialVector ∧ ProductOrder ∧ SelectedCoefficient
end LogicLineages.CartierObserverCurrent.FullSelectedCoefficient.Targets
