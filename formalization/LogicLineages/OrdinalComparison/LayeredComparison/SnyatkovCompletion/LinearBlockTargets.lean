module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockTargets
open NormalForm LinearBlock

/-- Stronger than name support: the unchanged occurrence itself survives
exactly when it is not named by the selected elimination variable. -/
def ExactOneNameOccurrences : Prop := ∀ (i : Nat) (p : Formula) (s : Summand),
  s ∈ occurrences (LinearRows.eliminate i p) ↔ s.name ≠ i ∧ s ∈ occurrences p

def ExactLinearityAfterElimination : Prop := ∀ (i j : Nat) (p : Formula),
  LinearRows.isLinear j (LinearRows.eliminate i p) =
    (if j = i then true else LinearRows.isLinear j p)

def ExactBlockTest : Prop := ∀ (names : List Nat) (p : Formula),
  allLinear names p = true ↔ ∀ i ∈ names, LinearRows.isLinear i p = true

/-- All original names, nonlinear free terms, signed coefficients, Boolean
positions and natural witnesses retain their source interpretation. -/
def ActualBlockElimination : Prop := ∀ (names : List Nat) (p : Formula),
  allLinear names p = true → ∀ ν : Nat → Nat,
    (eliminate names p).eval ν ↔ existsPrefix ν names p

def ExactBlockOccurrences : Prop := ∀ (names : List Nat) (p : Formula) (s : Summand),
  s ∈ occurrences (eliminate names p) ↔ s.name ∉ names ∧ s ∈ occurrences p

def ExactBlockSupport : Prop := ∀ (names : List Nat) (p : Formula) (v : Nat),
  v ∈ (eliminate names p).variables ↔ v ∉ names ∧ v ∈ p.variables

def LiteralCodeCalibration : Prop :=
  (∀ (names : List Nat) (p : Formula), LinearBlock.Code.allLinear names p.encode = allLinear names p) ∧
  (∀ (names : List Nat) (p : Formula), LinearBlock.Code.eliminate names p.encode = (eliminate names p).encode)

def ActualNumericPrograms : Prop := Primrec₂ LinearBlock.Code.allLinear ∧ Primrec₂ LinearBlock.Code.eliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockTargets
