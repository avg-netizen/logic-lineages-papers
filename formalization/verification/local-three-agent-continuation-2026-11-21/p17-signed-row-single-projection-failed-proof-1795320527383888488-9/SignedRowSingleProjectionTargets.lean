module
public import LogicLineages.PermittedControl.HighTailNamedRowProjectionTargets
public import LogicLineages.PermittedControl.SignedRowLowStripsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSingleProjection
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open MixedSameRankResidue (WeightedOperand weightedTailCode properOperand)
open MixedRankResidue (rankSupport)
open MixedRankNamedResidueRow (RawArgs rawArgs requests slots)
open HighTailNamedRowProjection (coordinateTail projectCode projected)
open SignedRowCoordinateSlice (Result denotes)
open SignedRowLowStrips (branches branchesCode encodeBranch)

abbrev Input := Nat × Nat × Nat × RawArgs
abbrev LowCode := List (Nat × Result LowerOperandCode)
abbrev HighCode := List NamedCode × Nat

/-- The two parts use the literal same effective tail. Every lower value
keeps its actual slice status, and the high packet keeps its request bytes. -/
noncomputable def compileCode (f : Nat → Nat) (input : Input) : Option (LowCode × HighCode) :=
  let (B,name,rank,q) := input
  let cutoff := weightedTailCode B q.1 q.2.2
  (projectCode (B,name,q)).map
    (fun high => (branchesCode f (rank,cutoff,q.2.1,q.2.2),high))

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (compileCode f)) ∧
  (∀ (f : Nat → Nat) (input : Input), input.2.2.2.1 = 0 → compileCode f input = none) ∧
  ∀ (f : Nat → Nat) (B m name rank : Nat) (c : Int) (terms : List WeightedOperand), 0 < m →
    compileCode f (B,name,rank,rawArgs m c terms) =
      some ((branches f rank (coordinateTail B m terms) c terms).map encodeBranch,
        (requests terms).map encodeRequest,(projected B m name c terms).encode)

def LowHit (f ρ : Nat → Nat) (B m rank : Nat) (c : Int) (terms : List WeightedOperand) : Prop :=
  ∃ (a : Nat) (b : Int) (rest : List WeightedOperand),
    (a,some (some (b,rest))) ∈ branches f rank (coordinateTail B m terms) c terms ∧
      denotes f (Function.update ρ rank a) m b rest

/-- Exactly one original rank is unrestricted. Every other used raw rank
keeps its original large value and its corresponding generated name. -/
def ActualCaseSplit : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m name rank : Nat) (c : Int) (terms : List WeightedOperand) (ρ ν : Nat → Nat),
    0 < m → (name,rank) ∈ slots terms → (∀ t ∈ terms, properOperand t.2) →
    (∀ r ∈ rankSupport terms, r ≠ rank → coordinateTail B m terms ≤ ρ r) →
    (∀ s ∈ slots terms, s.1 ≠ name → ν s.1 = ρ s.2) →
    ((∃ z : Nat, denotes f (Function.update ρ rank z) m c terms) ↔
      LowHit f ρ B m rank c terms ∨ (projected B m name c terms).eval ν)

def FullSignedRowSingleProjection : Prop := CodeExact ∧ ActualCaseSplit

end LogicLineages.PermittedControl.SignedRowSingleProjection
