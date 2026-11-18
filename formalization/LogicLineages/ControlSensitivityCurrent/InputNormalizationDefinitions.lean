module
public import LogicLineages.ControlSensitivityCurrent.PolicyCollisionDefinitions
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.InputNormalization
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering GroundEquivalence

/-- Natural references are actual typed ports; Boolean references point only backwards. -/
inductive Node (Γ : List Ty) (m : Nat) where
  | eq (a b : Port Γ) | le (a b : Port Γ) | lt (a b : Port Γ)
  | neg (a : Fin m) | conj (a b : Fin m) | disj (a b : Fin m)

def Node.rename {Γ Δ m} (r : Renaming Γ Δ) : Node Γ m → Node Δ m
  | .eq a b => .eq (ExistentialPlan.portRename r a) (ExistentialPlan.portRename r b)
  | .le a b => .le (ExistentialPlan.portRename r a) (ExistentialPlan.portRename r b)
  | .lt a b => .lt (ExistentialPlan.portRename r a) (ExistentialPlan.portRename r b)
  | .neg a => .neg a | .conj a b => .conj a b | .disj a b => .disj a b

def Node.eval {Γ m} (ρ : Variable Γ .ground → Nat) (v : Fin m → Bool) : Node Γ m → Bool
  | .eq a b => decide (a.value (ExistentialPlan.inputs ρ) = b.value (ExistentialPlan.inputs ρ))
  | .le a b => decide (a.value (ExistentialPlan.inputs ρ) ≤ b.value (ExistentialPlan.inputs ρ))
  | .lt a b => decide (a.value (ExistentialPlan.inputs ρ) < b.value (ExistentialPlan.inputs ρ))
  | .neg a => !(v a) | .conj a b => v a && v b | .disj a b => v a || v b

inductive Dag (Γ : List Ty) : Nat → Type where
  | nil : Dag Γ 0
  | snoc {m} : Dag Γ m → Node Γ m → Dag Γ (m+1)

def Dag.rename {Γ Δ} (r : Renaming Γ Δ) : {m : Nat} → Dag Γ m → Dag Δ m
  | _, .nil => .nil
  | _, .snoc d n => .snoc (d.rename r) (n.rename r)

def Dag.eval {Γ} (ρ : Variable Γ .ground → Nat) : {m : Nat} → Dag Γ m → Fin m → Bool
  | _, .nil => Fin.elim0
  | _, .snoc d n => Fin.cases (n.eval ρ (d.eval ρ)) (d.eval ρ)

def arity : Nat → Nat | 0 => 0 | m+1 => arity m+2

def mapNode {n k m} (r : Fin n → Fin k) : BooleanWire.Node n m → BooleanWire.Node k m
  | .eq a b => .eq (r a) (r b) | .le a b => .le (r a) (r b)
  | .lt a b => .lt (r a) (r b) | .neg a => .neg a
  | .conj a b => .conj a b | .disj a b => .disj a b

def mapDag {n k} (r : Fin n → Fin k) : {m : Nat} → BooleanWire.Dag n m → BooleanWire.Dag k m
  | _, .nil => .nil
  | _, .snoc d a => .snoc (mapDag r d) (mapNode r a)

/-- Two literal natural reference slots per Boolean node, even for logical nodes.
This is a linear, explicit reference-table expansion, not value evaluation. -/
def Node.ports {Γ m} : Node Γ m → Fin 2 → Port Γ
  | .eq a b | .le a b | .lt a b => Fin.cases a (fun _ => b)
  | _ => fun _ => .zero

def Node.wire {Γ m} : Node Γ m → BooleanWire.Node (arity m+2) m
  | .eq _ _ => .eq (Fin.natAdd (arity m) 0) (Fin.natAdd (arity m) 1)
  | .le _ _ => .le (Fin.natAdd (arity m) 0) (Fin.natAdd (arity m) 1)
  | .lt _ _ => .lt (Fin.natAdd (arity m) 0) (Fin.natAdd (arity m) 1)
  | .neg a => .neg a | .conj a b => .conj a b | .disj a b => .disj a b

def Dag.wires {Γ} : {m : Nat} → Dag Γ m → BooleanWire.Dag (arity m) m
  | _, .nil => .nil
  | _, .snoc d n => .snoc (mapDag (Fin.castAdd 2) d.wires) n.wire

def Dag.ports {Γ} : {m : Nat} → Dag Γ m → Fin (arity m) → Port Γ
  | _, .nil => Fin.elim0
  | _, .snoc d n => Fin.addCases d.ports n.ports

/-- Non-A-normal input: Boolean nodes may occur before, between or after natural
nodes. Natural outputs and Boolean outputs each have real backwards references.
An observation is the actual supplied source on the current shared context. -/
inductive Input : List Ty → Nat → Type where
  | finish {Γ m} : Fin m → Input Γ m
  | boolean {Γ m} : Node Γ m → Input Γ (m+1) → Input Γ m
  | add {Γ m} : Port Γ → Port Γ → Input (.ground::Γ) m → Input Γ m
  | literal {Γ m} : Nat → Input (.ground::Γ) m → Input Γ m
  | observation {Γ m} : GroundEquivalence.Input Γ .ground → Input (.ground::Γ) m → Input Γ m
  | unary {Γ m} : GroundEquivalence.Input [] (.arrow .ground .ground) →
      Variable Γ .ground → Input (.ground::Γ) m → Input Γ m

/-- Wire naturals use the observation convention rawScalar-1. Raw coordinates
used inside source interpretation remain rho+1. No identity between them is assumed. -/
noncomputable def sourceValue (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) (t : GroundEquivalence.Input Γ .ground) : Nat :=
  PolicyCollision.rawScalar p f (ExistentialPlan.inputs ρ) t.term - 1

noncomputable def Input.eval (p : AdmissibleSum.Policy) (f : Nat → Nat) :
    {Γ : List Ty} → {m : Nat} → (Variable Γ .ground → Nat) → (Fin m → Bool) → Input Γ m → Prop
  | _, _, _, v, .finish i => v i = true
  | _, _, ρ, v, .boolean n q => q.eval p f ρ (Fin.cases (n.eval ρ v) v)
  | _, _, ρ, v, .add a b q => q.eval p f (ExistentialPlan.extend ρ
      (a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ))) v
  | _, _, ρ, v, .literal k q => q.eval p f (ExistentialPlan.extend ρ k) v
  | _, _, ρ, v, .observation t q => q.eval p f (ExistentialPlan.extend ρ (sourceValue p f ρ t)) v
  | _, _, ρ, v, .unary h x q => q.eval p f
      (ExistentialPlan.extend ρ (sourceValue p f ρ (BooleanCompiler.call h x))) v

noncomputable def programEval (p : AdmissibleSum.Policy) (f : Nat → Nat) :
    {Γ : List Ty} → (Variable Γ .ground → Nat) → BooleanCompiler.Program Γ → Prop
  | _, ρ, .matrix d a root => BooleanWire.evaluate d (fun i => (a i).value (ExistentialPlan.inputs ρ)) root=true
  | _, ρ, .add a b q => programEval p f (ExistentialPlan.extend ρ
      (a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ))) q
  | _, ρ, .literal k q => programEval p f (ExistentialPlan.extend ρ k) q
  | _, ρ, .observation t q => programEval p f (ExistentialPlan.extend ρ (sourceValue p f ρ t)) q
  | _, ρ, .unary h x q => programEval p f
      (ExistentialPlan.extend ρ (sourceValue p f ρ (BooleanCompiler.call h x))) q

/-- Actual syntactic algorithm. Every natural node is emitted once; only the
accumulated Boolean references are lifted across a new natural wire. -/
def normalize : {Γ : List Ty} → {m : Nat} → Dag Γ m → Input Γ m → BooleanCompiler.Program Γ
  | _, _, d, .finish root => .matrix d.wires d.ports root
  | _, _, d, .boolean n q => normalize (.snoc d n) q
  | Γ, _, d, .add a b q => .add a b (normalize (d.rename (Renaming.weaken Γ .ground)) q)
  | Γ, _, d, .literal k q => .literal k (normalize (d.rename (Renaming.weaken Γ .ground)) q)
  | Γ, _, d, .observation t q => .observation t (normalize (d.rename (Renaming.weaken Γ .ground)) q)
  | Γ, _, d, .unary h x q => .unary h x (normalize (d.rename (Renaming.weaken Γ .ground)) q)

def Input.cost : {Γ : List Ty} → {m : Nat} → Input Γ m → Nat
  | _, _, .finish _ => 1
  | _, _, .boolean _ q => 3+q.cost
  | _, _, .add _ _ q | _, _, .observation _ q => 1+q.cost
  | _, _, .literal k q => Nat.log2 k+2+q.cost
  | _, _, .unary _ _ q => 3+q.cost

def Input.sourceMax : {Γ : List Ty} → {m : Nat} → Input Γ m → Nat
  | _, _, .finish _ => 0
  | _, _, .boolean _ q | _, _, .add _ _ q | _, _, .literal _ q => q.sourceMax
  | _, _, .observation t q => max t.specs.length q.sourceMax
  | _, _, .unary h _ q => max h.specs.length q.sourceMax
end LogicLineages.ControlSensitivityCurrent.InputNormalization
