module
public import LogicLineages.PermittedControl.PureSuccessorTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Literal final pure-square count, its actual entry norm and source ceiling
identity, including target zero. No stopping-time supplier is assumed. -/
def ActualTerminalSquare : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu A : Ordinal.{0}) (R t : Nat), mu < epsilonZero → A < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → 20 ≤ R → actualOrdinalNorm mu ≤ R →
  thickBlockTail R B ≤ t → actualLimitPart A=mu+Ordinal.omega0^(2 : Ordinal) → actualOrdinalNorm A=t →
  let c := relativeProfile mu 1
  let q := (f t-c)/2
  FirstEntry f A mu (1+q) ∧ entryNormAt f A (1+q)=f^[1+q] t ∧
    q=f t/2-(c+1)/2

/-- Exact source terminal sign, including equality, for actual pure-square
states of common norm and potentially different finite tails. -/
def ActualTerminalSquareComparison : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu A A' : Ordinal.{0}) (R t : Nat),
  mu < epsilonZero → nu < epsilonZero → A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  20 ≤ R → actualOrdinalNorm mu ≤ R → actualOrdinalNorm nu ≤ R → thickBlockTail R B ≤ t →
  actualLimitPart A=mu+Ordinal.omega0^(2 : Ordinal) →
  actualLimitPart A'=nu+Ordinal.omega0^(2 : Ordinal) → actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  let q := (f t-relativeProfile mu 1)/2
  let q' := (f t-relativeProfile nu 1)/2
  FirstEntry f A mu (1+q) ∧ FirstEntry f A' nu (1+q') ∧
    compare (entryNormAt f A (1+q)) (entryNormAt f A' (1+q'))=
      compare ((relativeProfile nu 1+1)/2) ((relativeProfile mu 1+1)/2)

/-- E=1 boundary: genuine event-one entry and actual norm, with no positive
retained-prefix requirement and no terminal nonfiniteness assumption. -/
def ActualTerminalOmega : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu A : Ordinal.{0}) (t : Nat), mu < epsilonZero → A < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → actualLimitPart A=mu+Ordinal.omega0 → actualOrdinalNorm A=t →
  FirstEntry f A mu 1 ∧ entryNormAt f A 1=f t

def TerminalPhaseFoundation : Prop := ActualTerminalSquare ∧ ActualTerminalSquareComparison ∧ ActualTerminalOmega

end LogicLineages.PermittedControl.Targets
