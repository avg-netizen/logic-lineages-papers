module
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence PrimitiveLowering

/-- Literal natural expressions before flattening. Source leaves retain the
actual typed shared source table and original free-name context. -/
inductive Term (Γ : List Ty) where
  | var : Variable Γ .ground → Term Γ
  | literal : Nat → Term Γ
  | add : Term Γ → Term Γ → Term Γ
  | unary : Input [] (.arrow .ground .ground) → Term Γ → Term Γ
  | observation : Input Γ .ground → Term Γ

/-- Closed supplied function on the natural/raw convention from def:source-language. -/
noncomputable def callValue (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (h : Input [] (.arrow .ground .ground)) (n : Nat) : Nat :=
  InputNormalization.sourceValue p f (ExistentialPlan.extend (fun x : Variable [] .ground => nomatch x) n)
    (BooleanCompiler.call h (Variable.here : Variable [.ground] .ground))

noncomputable def Term.eval (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) : Term Γ → Nat
  | .var x => ρ x
  | .literal k => k
  | .add a b => a.eval p f ρ + b.eval p f ρ
  | .unary h a => callValue p f h (a.eval p f ρ)
  | .observation t => InputNormalization.sourceValue p f ρ t

/-- Each continuation receives the actual typed embedding of all its old
names and the returned natural port, not a semantic value or syntax oracle. -/
abbrev Continuation (Γ : List Ty) (m : Nat) :=
  ∀ {Δ : List Ty}, Renaming Γ Δ → Port Δ → InputNormalization.Input Δ m

/-- Concrete structural CPS compiler. Addition evaluates each argument once.
A unary argument is put in a fresh wire by adding zero, then the actual closed
source is applied to that wire. This uniform extra node avoids a hidden port case. -/
def Term.emit {Γ} : Term Γ → {Δ : List Ty} → {m : Nat} →
    Renaming Γ Δ → Continuation Δ m → InputNormalization.Input Δ m
  | .var x, _, _, r, k => k (fun y => y) (.var (r x))
  | .literal n, Δ, _, _, k => .literal n (k (Renaming.weaken Δ .ground) (.var .here))
  | .observation t, Δ, _, r, k =>
      .observation (ScopedDAG.renameInput r t) (k (Renaming.weaken Δ .ground) (.var .here))
  | .add a b, _, _, r, k => a.emit r (fun s av =>
      b.emit (fun x => s (r x)) (fun t bv =>
        .add (ExistentialPlan.portRename t av) bv
          (k (fun x => .there (t (s x))) (.var .here))))
  | .unary h a, _, _, r, k => a.emit r (fun s av =>
      .add av .zero (.unary h .here (k (fun x => .there (.there (s x))) (.var .here))))

/-- AST occurrence budget, NOT a shared-DAG expansion bound. -/
def Term.cost {Γ} : Term Γ → Nat
  | .var _ => 0
  | .literal n => Nat.log2 n+2
  | .add a b => a.cost+b.cost+1
  | .unary _ a => a.cost+4
  | .observation _ => 1

def Term.sourceMax {Γ} : Term Γ → Nat
  | .var _ | .literal _ => 0
  | .add a b => max a.sourceMax b.sourceMax
  | .unary h a => max h.specs.length a.sourceMax
  | .observation t => t.specs.length
end LogicLineages.ControlSensitivityCurrent.SourceAST
