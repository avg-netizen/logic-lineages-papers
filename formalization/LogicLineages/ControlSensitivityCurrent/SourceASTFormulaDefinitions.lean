module
public import LogicLineages.ControlSensitivityCurrent.SourceASTDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering

/-- Literal quantifier-free matrix. Quantifiers belong to the explicit sentence
prefix, never beneath negation. Supplied sources live in the natural Term leaves. -/
inductive Formula (Γ : List Ty) where
  | truth | falsity
  | eq : Term Γ → Term Γ → Formula Γ
  | le : Term Γ → Term Γ → Formula Γ
  | lt : Term Γ → Term Γ → Formula Γ
  | neg : Formula Γ → Formula Γ
  | conj : Formula Γ → Formula Γ → Formula Γ
  | disj : Formula Γ → Formula Γ → Formula Γ

noncomputable def Formula.eval (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) : Formula Γ → Bool
  | .truth => true | .falsity => false
  | .eq a b => decide (a.eval p f ρ = b.eval p f ρ)
  | .le a b => decide (a.eval p f ρ ≤ b.eval p f ρ)
  | .lt a b => decide (a.eval p f ρ < b.eval p f ρ)
  | .neg a => !(a.eval p f ρ)
  | .conj a b => a.eval p f ρ && b.eval p f ρ
  | .disj a b => a.eval p f ρ || b.eval p f ρ

abbrev BooleanContinuation (Γ : List Ty) (m : Nat) :=
  ∀ {Δ : List Ty} {n : Nat}, Renaming Γ Δ → (Fin m → Fin n) → Fin n → InputNormalization.Input Δ n

/-- One literal relation node after both natural AST operands have been compiled
once; their returned typed embeddings are composed rather than discarded. -/
def emitRelation {Γ Δ m} (a b : Term Γ) (r : Renaming Γ Δ)
    (node : ∀ {Ξ n}, Port Ξ → Port Ξ → InputNormalization.Node Ξ n)
    (k : BooleanContinuation Δ m) : InputNormalization.Input Δ m :=
  a.emit r (fun s av => b.emit (fun x => s (r x)) (fun t bv =>
    .boolean (node (ExistentialPlan.portRename t av) bv)
      (k (fun x => t (s x)) Fin.succ 0)))

def Formula.emit {Γ} : Formula Γ → {Δ : List Ty} → {m : Nat} →
    Renaming Γ Δ → BooleanContinuation Δ m → InputNormalization.Input Δ m
  | .truth, _, _, _, k => .boolean (.eq .zero .zero) (k (fun x => x) Fin.succ 0)
  | .falsity, _, _, _, k => .boolean (.lt .zero .zero) (k (fun x => x) Fin.succ 0)
  | .eq a b, _, _, r, k => emitRelation a b r (fun a b => .eq a b) k
  | .le a b, _, _, r, k => emitRelation a b r (fun a b => .le a b) k
  | .lt a b, _, _, r, k => emitRelation a b r (fun a b => .lt a b) k
  | .neg a, _, _, r, k => a.emit r (fun s e root =>
      .boolean (.neg root) (k s (fun i => (e i).succ) 0))
  | .conj a b, _, _, r, k => a.emit r (fun s e left =>
      b.emit (fun x => s (r x)) (fun t h right =>
        .boolean (.conj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)))
  | .disj a b, _, _, r, k => a.emit r (fun s e left =>
      b.emit (fun x => s (r x)) (fun t h right =>
        .boolean (.disj (h left) right) (k (fun x => t (s x)) (fun i => (h (e i)).succ) 0)))

def Formula.toInput {Γ} (a : Formula Γ) : InputNormalization.Input Γ 0 :=
  a.emit (fun x => x) (fun _ _ root => .finish root)

def Formula.toProgram {Γ} (a : Formula Γ) : BooleanCompiler.Program Γ :=
  InputNormalization.normalize .nil a.toInput

def Formula.cost {Γ} : Formula Γ → Nat
  | .truth | .falsity => 3
  | .eq a b | .le a b | .lt a b => a.cost+b.cost+3
  | .neg a => a.cost+3
  | .conj a b | .disj a b => a.cost+b.cost+3

def Formula.sourceMax {Γ} : Formula Γ → Nat
  | .truth | .falsity => 0
  | .eq a b | .le a b | .lt a b => max a.sourceMax b.sourceMax
  | .neg a => a.sourceMax
  | .conj a b | .disj a b => max a.sourceMax b.sourceMax

/-- The finite existential prefix is actual ground variables, one shared
valuation. This definition does not claim prenexing of a larger syntax. -/
structure Sentence where
  «variables» : Nat
  matrix : Formula (List.replicate «variables» Ty.ground)
noncomputable def Sentence.holds (p : AdmissibleSum.Policy) (f : Nat → Nat) (s : Sentence) : Prop :=
  ∃ ρ : Variable (List.replicate s.variables Ty.ground) .ground → Nat,
    s.matrix.eval p f ρ = true
end LogicLineages.ControlSensitivityCurrent.SourceAST
