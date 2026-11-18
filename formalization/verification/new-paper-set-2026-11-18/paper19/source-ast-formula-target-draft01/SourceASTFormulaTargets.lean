module
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceASTFormulaTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAST
/-- Every old natural coordinate and Boolean wire is part of the continuation
specification. The final callback is proved, not assumed, in Concrete below. -/
def CPS : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ Δ : List Ty) (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat)
  (ν : Variable Δ .ground → Nat), (∀ x, ν (r x)=ρ x) →
  ∀ (m : Nat) (v : Fin m → Bool) (a : Formula Γ) (k : BooleanContinuation Δ m) (P : Bool → Prop),
  (∀ (Ξ : List Ty) (n : Nat) (s : Renaming Δ Ξ) (e : Fin m → Fin n)
    (μ : Variable Ξ .ground → Nat) (w : Fin n → Bool),
    (∀ x, μ (s x)=ν x) → (∀ i, w (e i)=v i) → ∀ root : Fin n,
    (k s e root).eval p f μ w ↔ P (w root)) →
  ((a.emit r k).eval p f ν v ↔ P (a.eval p f ρ))

def Budgets : Prop := ∀ (Γ Δ : List Ty) (m : Nat) (r : Renaming Γ Δ)
  (a : Formula Γ) (k : BooleanContinuation Δ m) (K M : Nat),
  (∀ (Ξ : List Ty) (n : Nat) (s : Renaming Δ Ξ) (e : Fin m → Fin n) (root : Fin n),
    (k s e root).cost ≤ K ∧ (k s e root).sourceMax ≤ M) →
  ((a.emit r k).cost ≤ a.cost+K ∧ (a.emit r k).sourceMax ≤ max a.sourceMax M)

/-- Full literal quantifier-free AST coverage, including concrete finish callback,
then actual interleaved-to-A-normal normalization at the same source valuation. -/
def Concrete : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : Variable Γ .ground → Nat) (a : Formula Γ),
  (a.toInput.eval p f ρ Fin.elim0 ↔ a.eval p f ρ = true) ∧
  (InputNormalization.programEval p f ρ a.toProgram ↔ a.eval p f ρ = true)

def ConcreteBudgets : Prop := ∀ (Γ : List Ty) (a : Formula Γ),
  a.toProgram.codeSize ≤ a.cost+1 ∧ a.toProgram.sourceMax ≤ a.sourceMax ∧
  a.toProgram.load ≤ (a.cost+1)*(a.sourceMax+1)

def Prefix : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (s : Sentence),
  s.holds p f ↔ ∃ ρ : Variable (List.replicate s.variables Ty.ground) .ground → Nat,
    InputNormalization.programEval p f ρ s.matrix.toProgram
end LogicLineages.ControlSensitivityCurrent.SourceASTFormulaTargets
