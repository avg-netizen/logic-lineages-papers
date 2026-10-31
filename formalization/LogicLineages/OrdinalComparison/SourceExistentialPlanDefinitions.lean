module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan
open GroundEquivalence PrimitiveLowering

/-- Ground coordinates are naturals; any unused functional coordinates are
fixed to the genuine common unit. -/
def inputs {Γ} (ρ : Variable Γ .ground → Nat) : OrdinalComponent Γ → Nat
  | ⟨.ground,x,_⟩ => ρ x
  | ⟨.arrow _ _,_,_⟩ => 0
def extend {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) : Variable (.ground::Γ) .ground → Nat
  | .here => n
  | .there x => ρ x

def portRename {Γ Δ} (r : Renaming Γ Δ) : Port Γ → Port Δ
  | .zero => .zero
  | .var x => .var (r x)
def gateRename {Γ Δ} (r : Renaming Γ Δ) : Gate Γ → Gate Δ
  | .eq a b => .eq (portRename r a) (portRename r b)
  | .add a b c => .add (portRename r a) (portRename r b) (portRename r c)
  | .sort a b l h => .sort (portRename r a) (portRename r b) (portRename r l) (portRename r h)
  | .one a => .one (portRename r a)

/-- Explicit finite existential/conjunctive syntax. Source leaves contain
actual primitive DAGs, not arbitrary predicates or functional graph oracles. -/
inductive Plan : List Ty → Type where
  | done {Γ} : Plan Γ
  | equation {Γ} : Input Γ .ground → Input Γ .ground → Plan Γ → Plan Γ
  | gate {Γ} : Gate Γ → Plan Γ → Plan Γ
  | existsGround {Γ} : Plan (.ground::Γ) → Plan Γ
noncomputable def Eval {Γ} (ρ : Variable Γ .ground → Nat) : Plan Γ → Prop
  | .done => True
  | .equation a b q => SourceAdditionCompletion.Equation (inputs ρ) a.term b.term ∧ Eval ρ q
  | .gate g q => g.Holds (inputs ρ) ∧ Eval ρ q
  | .existsGround q => ∃ n, Eval (extend ρ n) q

def Plan.vertices {Γ} : Plan Γ → Nat
  | .done => 0
  | .equation a b q => a.specs.length+b.specs.length+q.vertices
  | .gate _ q => 80+q.vertices
  | .existsGround q => q.vertices
def Plan.equations {Γ} : Plan Γ → Nat
  | .done => 0
  | .equation _ _ q => 1+q.equations
  | .gate _ q => 10+q.equations
  | .existsGround q => q.equations
def Plan.witnesses {Γ} : Plan Γ → Nat
  | .done => 0
  | .equation _ _ q => q.witnesses
  | .gate _ q => 9+q.witnesses
  | .existsGround q => 1+q.witnesses

structure Result (Γ : List Ty) where
  context : List Ty
  embedding : Renaming Γ context
  forest : List (Input context .ground × Input context .ground)

def compile {Γ} : Plan Γ → Result Γ
  | .done => ⟨Γ,(fun x => x),[]⟩
  | .equation a b q =>
    let r := compile q
    ⟨r.context,r.embedding,
      (ScopedDAG.renameInput r.embedding a,ScopedDAG.renameInput r.embedding b)::r.forest⟩
  | .gate g q =>
    let r := compile q
    ⟨Block r.context,(fun x => shift 9 (r.embedding x)),
      forest (gateRename r.embedding g) ++ r.forest.map
        (fun e => (ScopedDAG.renameInput (shift 9) e.1,ScopedDAG.renameInput (shift 9) e.2))⟩
  | .existsGround q =>
    let r := compile q
    ⟨r.context,(fun x => r.embedding (.there x)),r.forest⟩
noncomputable def Result.Holds {Γ} (r : Result Γ) (ρ : Variable r.context .ground → Nat) : Prop :=
  ∀ e ∈ r.forest, SourceAdditionCompletion.Equation (inputs ρ) e.1.term e.2.term
def Result.nodes {Γ} (r : Result Γ) : Nat :=
  (r.forest.map (fun e => e.1.specs.length+e.2.specs.length)).sum

def strictPair {Γ} (q : Plan Γ) : Input (compile q).context .ground × Input (compile q).context .ground :=
  let a := ScopedDAG.aggregate (compile q).forest
  (a.2,a.1)
def weakPair {Γ} (q : Plan Γ) : Input (compile q).context .ground × Input (compile q).context .ground :=
  (upperInput (strictPair q).1,lowerInput (strictPair q).2)
end LogicLineages.OrdinalComparison.Source.ExistentialPlan
