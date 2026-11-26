module
public import LogicLineages.StandardControlCurrent.NumericalKernelDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelTargets
open OrdinalComparison NumericalKernel

def Process : Prop := ∀ d c t : Nat, 1 ≤ d → c ≤ Phi t →
  first d c t < Ordinal.omega0 ^ (d : Ordinal) ∧
  actualOrdinalNorm (first d c t) = Phi t-c ∧
  0 < count d c t ∧ state d c t (count d c t) < Ordinal.omega0 ∧
  (∀ i : Nat, i < count d c t → Ordinal.omega0 ≤ state d c t i) ∧
  (∀ i : Nat, 1 ≤ i → i ≤ count d c t →
    c + actualOrdinalNorm (state d c t i) = (Phi^[i]) t) ∧
  (∀ i : Nat, i < count d c t →
    state d c t (i+1) = actualMaximumPredecessor (actualLimitPart (state d c t i))
      ((Phi^[i+1]) t-c))

def PaddedAgreement : Prop := ∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
  count d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
  value d c t = actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t

def Bases : Prop :=
  (∀ c t : Nat, c ≤ Phi t → count 1 c t = 1 ∧ value 1 c t = Phi t) ∧
  (∀ c t : Nat, c ≤ Phi t → count 2 c t = Phi t/2-(c+1)/2+1) ∧
  (∀ c t : Nat, c ≤ Phi t → ∀ j : Int,
    depth 2 c j t = ((Phi t/2 : Nat) : Int)+(j-(((c+1)/2 : Nat) : Int))+1 ∧
    signed 2 c j t = rawQuadraticShift (j-(((c+1)/2 : Nat) : Int)) t) ∧
  (∀ c : Nat, ∀ j : Int, ∀ t : Nat,
    finiteKernelRecursionThreshold 2 c j ≤ t → 0 < depth 2 c j t)

def Recurrences : Prop :=
  (∀ n c t : Nat, c+2*(n+2)+1 ≤ t →
    let entry := value (n+2) (c+n+2) t
    count (n+2) c t = count (n+1) c entry + count (n+2) (c+n+2) t ∧
    value (n+2) c t = value (n+1) c entry) ∧
  (∀ n c : Nat, ∀ j : Int, (1 ≤ n ∨ 0 ≤ j) → ∀ t : Nat,
    finiteKernelRecursionThreshold (n+2) c j ≤ t →
    let entry := value (n+2) (c+n+2) t
    0 < depth (n+2) c j t ∧ 0 < depth (n+1) c j entry ∧
    signed (n+2) c j t = signed (n+1) c j entry)

def Programs : Prop :=
  Computable (fun x : Nat × Nat × Nat => countCode x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × Nat => valueCode x.1 x.2.1 x.2.2) ∧
  (∀ d c t : Nat, 1 ≤ d → c ≤ Phi t →
    countCode d c t = count d c t ∧ valueCode d c t = value d c t) ∧
  Computable (fun x : Nat × Nat × Int => finiteKernelRecursionThreshold x.1 x.2.1 x.2.2)

def Full : Prop := Process ∧ PaddedAgreement ∧ Bases ∧ Recurrences ∧ Programs
end LogicLineages.StandardControlCurrent.NumericalKernelTargets
