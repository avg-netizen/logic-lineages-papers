module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionTargets
open NormalForm PlainParameterDecision

def ExactFixedNames : Prop := ∀ (xs : List Nat) (p : Formula) (i : Nat),
  i ∈ fixedNames xs p ↔ i ∈ p.variables ∧ i ∉ xs

def ExactFrame : Prop := ∀ (xs values : List Nat) (p : Formula) (σ : Nat → Nat),
  (frame xs values p).eval σ ↔ p.eval σ ∧ ∀ i ∈ p.variables, i ∉ xs → σ i = valuation values i

def ActualParameterizedExistential : Prop := ∀ (xs values : List Nat) (p : Formula),
  PlainLinearCleanup.Satisfiable (frame xs values p) ↔ existsPrefix (valuation values) xs p

def ActualParameterizedUniversal : Prop := ∀ (xs values : List Nat) (p : Formula),
  (¬PlainLinearCleanup.Satisfiable (frame xs values (.negative p))) ↔ forallPrefix (valuation values) xs p

def PreservePlain : Prop := ∀ (xs values : List Nat) (p : Formula), MaximalPlainBranch.isPlain p = true →
  MaximalPlainBranch.isPlain (frame xs values p) = true

def ExactDecisionDomains : Prop := ∀ (xs values : List Nat) (p : Formula),
  (decideExists xs values p).isSome = MaximalPlainBranch.isPlain p ∧
    (decideForall xs values p).isSome = MaximalPlainBranch.isPlain p

def ActualDecisions : Prop := ∀ (xs values : List Nat) (p : Formula), MaximalPlainBranch.isPlain p = true → ∀ b : Bool,
  (decideExists xs values p = some b ↔ (existsPrefix (valuation values) xs p ↔ b = true)) ∧
    (decideForall xs values p = some b ↔ (forallPrefix (valuation values) xs p ↔ b = true))

def LiteralCodeData : Prop := ∀ (xs values : List Nat) (p : Formula),
  Code.frame xs values p.encode = (frame xs values p).encode ∧
    Code.decideExists xs values p.encode = decideExists xs values p ∧
    Code.decideForall xs values p.encode = decideForall xs values p

def ActualNumericPrograms : Prop :=
  Primrec (fun p : List Nat × (List Nat × Nat) => Code.frame p.1 p.2.1 p.2.2) ∧
    Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideExists p.1 p.2.1 p.2.2) ∧
    Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideForall p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionTargets
