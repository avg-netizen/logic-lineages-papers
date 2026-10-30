module
public import LogicLineages.OrdinalComparison.BinaryObserverDefinitions
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof

@[expose] public section

/-! Full selected-coefficient source comparator, paper10 thm:observer,
paper.tex419–433. Actual partition counts, every denominator factor, field
cancellations, literal e0 and the reversed noncommutative matrix product are
retained. Every LSB-first bit representation is allowed, including empty
and redundant leading-zero words. The Nat-valued gate identifies parity
without confusing a field element with an ordinary unbounded count. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryInitialVectorCalibration : Prop :=
  ∀ D : Nat, actualBinaryCoefficientVector D (1 : Polynomial (ZMod 2)) =
    actualBinaryInitialVector D

def ActualBinaryMatrixWordProduct : Prop :=
  ∀ (K : Type u) [Field K], ∀ D : Nat, ∀ A : Polynomial K,
    ∀ w : List Bool, ∀ v : Fin D → K,
      actualBinaryMatrixWord D A w v =
        Matrix.mulVec ((w.reverse.map (actualBinaryTransitionMatrix D A)).prod) v

def ActualSourceBinarySelectedCoefficient : Prop :=
  ∀ d : Nat, ∀ hd : 0 < d, ∀ n : Nat, ∀ w : List Bool,
    actualBinaryWordValue w = n →
      Matrix.mulVec
        ((w.reverse.map (actualBinaryTransitionMatrix (actualBinarySourceDimension d)
          (actualBinarySourceDenominator d))).prod)
        (actualBinaryInitialVector (actualBinarySourceDimension d))
        ⟨0, actualBinarySourceDimensionPositive d hd⟩ =
      (restrictedPartitionCount d n : ZMod 2)

def ActualSourceBinarySelectedParity : Prop :=
  ∀ d : Nat, ∀ hd : 0 < d, ∀ n : Nat, ∀ w : List Bool,
    actualBinaryWordValue w = n →
      (Matrix.mulVec
        ((w.reverse.map (actualBinaryTransitionMatrix (actualBinarySourceDimension d)
          (actualBinarySourceDenominator d))).prod)
        (actualBinaryInitialVector (actualBinarySourceDimension d))
        ⟨0, actualBinarySourceDimensionPositive d hd⟩).val =
      restrictedPartitionCount d n % 2

end LogicLineages.OrdinalComparison.Targets
