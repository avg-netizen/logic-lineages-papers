module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanTargets
open CommonLayerSyntax CommonHeadBoolean

def ExactTranslation : Prop := ∀ (Γ : List NONote), genuineHeads Γ →
  ∀ (p : Formula) (ν : Nat → Nat), (translate (headCodes Γ) p).eval ν ↔ p.eval (headCodes Γ) ν

def ExactPrefixTranslation : Prop := ∀ (Γ : List NONote), genuineHeads Γ →
  ∀ (xs : List Nat) (p : Formula) (ν : Nat → Nat),
  (BaseBooleanSource.existsPrefix ν xs (translate (headCodes Γ) p) ↔ existsPrefix (headCodes Γ) ν xs p) ∧
    (BaseBooleanSource.forallPrefix ν xs (translate (headCodes Γ) p) ↔ forallPrefix (headCodes Γ) ν xs p)

/-- Literal stack equality is unconditional on all raw head lists and source
formulas, including Boolean negation and disjunction in original positions. -/
def LiteralStackCompiler : Prop := ∀ (heads : List Nat) (p : Formula) (stack : Code.Stack),
  Code.run heads p.encode stack = (translate heads p).encode :: stack

def ActualBlockDecisions : Prop := ∀ (Γ : List NONote), genuineHeads Γ →
  ∀ (xs values : List Nat) (p : Formula) (b : Bool),
  (Code.decideExists (headCodes Γ) xs values p.encode = some b ↔
    (existsPrefix (headCodes Γ) (PlainParameterDecision.valuation values) xs p ↔ b = true)) ∧
  (Code.decideForall (headCodes Γ) xs values p.encode = some b ↔
    (forallPrefix (headCodes Γ) (PlainParameterDecision.valuation values) xs p ↔ b = true))

def ActualClosureDecisions : Prop := ∀ (Γ : List NONote), genuineHeads Γ →
  ∀ (p : Formula) (b : Bool),
  (Code.decideClosureExists (headCodes Γ) p.encode = some b ↔ ((∃ ν : Nat → Nat, p.eval (headCodes Γ) ν) ↔ b = true)) ∧
  (Code.decideClosureForall (headCodes Γ) p.encode = some b ↔ ((∀ ν : Nat → Nat, p.eval (headCodes Γ) ν) ↔ b = true))

/-- Actual programs on all raw inputs; no malformed-postfix semantic claim. -/
def ActualAllCodePrograms : Prop :=
  Computable (fun p : List Nat × (CommonHeadCompiler.Instruction × Code.Stack) => Code.step p.1 p.2.1 p.2.2) ∧
  Computable (fun p : List Nat × (Code.Program × Code.Stack) => Code.run p.1 p.2.1 p.2.2) ∧
  Computable₂ Code.compile ∧
  Computable (fun p : List Nat × (List Nat × (List Nat × Code.Program)) => Code.decideExists p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Computable (fun p : List Nat × (List Nat × (List Nat × Code.Program)) => Code.decideForall p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Computable₂ Code.decideClosureExists ∧ Computable₂ Code.decideClosureForall

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanTargets
