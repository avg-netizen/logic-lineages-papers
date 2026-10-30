module
public import LogicLineages.OrdinalComparison.SeriesObservabilityDefinitions
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- The source binary coefficient selector Lambda_b: retain coefficients
whose indices have the supplied low bit, then remove that bit. -/
noncomputable def actualBinarySeriesDigit {K : Type u} [Field K] (b : Bool)
    (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => PowerSeries.coeff (Nat.bit b n) F

/-- Execute a continuation from its least significant bit onward. -/
noncomputable def actualBinarySeriesWord {K : Type u} [Field K] :
    List Bool → PowerSeries K → PowerSeries K
  | [], F => F
  | b :: w, F => actualBinarySeriesWord w (actualBinarySeriesDigit b F)

def actualBinaryWordValue : List Bool → Nat
  | [] => 0
  | b :: w => Nat.bit b (actualBinaryWordValue w)

end LogicLineages.OrdinalComparison
