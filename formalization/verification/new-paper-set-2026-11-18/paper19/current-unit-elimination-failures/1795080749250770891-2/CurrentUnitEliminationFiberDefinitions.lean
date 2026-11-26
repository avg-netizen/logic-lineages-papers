module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open CurrentOneUnit

def functionalCount : List Ty → Nat
  | [] => 0
  | .ground :: Γ => functionalCount Γ
  | .arrow _ _ :: Γ => functionalCount Γ + 1

/-- All external original ground wires are read exactly once from their
original valuation. Internal values are encoded, raw = encoded + 1. -/
noncomputable def HoldsRaw {Γ : List Ty} (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (q : OpenGraph Γ) (ρ : Variable Γ .ground → Nat) (r : Nat) : Prop :=
  ∃ n, n+1 = r ∧ q.holds p f ρ n

noncomputable def Tree.holds {Γ : List Ty} (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (q : Tree Γ) (ρ : Variable Γ .ground → Nat) (r : Nat) : Prop :=
  HoldsRaw p f (render p f q) (fun x => ρ (oldGround x)) r

noncomputable def EveryScalarUnique (p : AdmissibleSum.Policy) (f : Nat → Nat) :
    {Γ : List Ty} → Tree Γ → Prop
  | _,.leaf _ _ => True
  | _,.free _ _ _ _ _ q => unique q ∧ EveryScalarUnique p f q
  | _,.active _ _ _ _ _ q r =>
      unique q ∧ unique r ∧ EveryScalarUnique p f q ∧ EveryScalarUnique p f r
where
  unique {Γ : List Ty} (q : Tree Γ) :=
    ∀ (ρ : Variable Γ .ground → Nat) (a b : Nat), q.holds p f ρ a → q.holds p f ρ b → a=b

/-- Literal syntax subset used by the graph. Each observation is an actual
typed ground source, not an externally supplied graph predicate. -/
def LinearTerm {Γ : List Ty} : SourceAST.Term Γ → Prop
  | .var _ | .literal _ | .observation _ => True
  | .add a b => LinearTerm a ∧ LinearTerm b
  | .unary _ _ => False

def Conjunctive {Γ : List Ty} : SourceAST.Formula Γ → Prop
  | .truth => True
  | .eq a b => LinearTerm a ∧ LinearTerm b
  | .conj a b => Conjunctive a ∧ Conjunctive b
  | _ => False

/-- Attach exact equalities fixing the original shared ground variables.
The binder prefix only existentially selects the remaining wires. -/
def pinGround : (Γ : List Ty) → {Δ : List Ty} →
    (Variable Γ .ground → Variable Δ .ground) → (Variable Γ .ground → Nat) → SourceAST.Formula Δ
  | [],_,_,_ => .truth
  | .ground :: Γ,_,r,ρ =>
    .conj (.eq (.var (r .here)) (.literal (ρ .here)))
      (pinGround Γ (fun x => r (.there x)) (fun x => ρ (.there x)))
  | .arrow _ _ :: Γ,_,r,ρ => pinGround Γ (fun x => r (.there x)) (fun x => ρ (.there x))

theorem groundWireCtx (n : Nat) (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) :
    ∀ σ ∈ WireCtx n Γ, σ = .ground := by
  induction n with
  | zero => exact hg
  | succ n ih => simp [WireCtx,ih]

theorem allGroundReplicate (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) :
    Γ = List.replicate Γ.length Ty.ground := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hs := hg σ (by simp)
    obtain rfl := hs
    simp only [List.length_cons, List.replicate_succ]
    exact congrArg (List.cons Ty.ground) (ih (fun t ht => hg t (by simp [ht])))

/-- Close one fixed input/result fiber using the exact current SourceAST
sentence grammar consumed by the checked Boolean compiler. This does not
replace the open free-variable definition with mere global satisfiability. -/
def closeFiber {Γ : List Ty} (g : OpenGraph Γ) (hg : ∀ σ ∈ Γ, σ = .ground)
    (ρ : Variable Γ .ground → Nat) (n : Nat) : SourceAST.Sentence :=
  let Δ := WireCtx g.width (.ground :: Γ)
  let e : Δ = List.replicate Δ.length .ground :=
    allGroundReplicate Δ (groundWireCtx g.width _
      (fun σ h => by rcases List.mem_cons.mp h with rfl|h; rfl; exact hg σ h))
  let rows := SourceAST.Formula.conj
    (.eq (.var (shift g.width .here)) (.literal n))
    (pinGround Γ (fun x => shift g.width (.there x)) ρ)
  ⟨Δ.length,e ▸ SourceAST.Formula.conj g.matrix rows⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
