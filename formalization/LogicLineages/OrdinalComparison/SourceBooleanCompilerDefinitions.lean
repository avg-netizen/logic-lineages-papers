module
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceBooleanPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanCompiler
open OriginalDomain GroundEquivalence PrimitiveLowering

def emptyRename (Γ : List Ty) : Renaming [] Γ := fun x => nomatch x
/-- The extra unary function is literally the supplied closed original source
applied to the same named ground input. Its full canonical assignment is used. -/
def call {Γ} (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground) : Input Γ .ground :=
  ScopedDAG.application (ScopedDAG.renameInput (emptyRename Γ) h) (ScopedDAG.variableInput x)
noncomputable def sourceValue {Γ} (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground) : Nat :=
  SourceCollisionCompletion.rawScalar (valuation (UnitObservation.substitution ρ)) t.term-1

/-- A finite A-normal arithmetic/Boolean DAG encoding of existential E_source.
Each arithmetic/source node binds ONE shared output wire; subsequent nodes
refer to it by the same typed variable. The terminal Boolean DAG has explicit
backwards references, and arbitrary source DAGs retain their internal sharing.
There are no assumed arithmetic equations or semantic predicate leaves. -/
inductive Program : List Ty → Type where
  | matrix {Γ n m} : BooleanWire.Dag n m → (Fin n → Port Γ) → Fin m → Program Γ
  | add {Γ} : Port Γ → Port Γ → Program (.ground::Γ) → Program Γ
  | literal {Γ} : Nat → Program (.ground::Γ) → Program Γ
  | observation {Γ} : Input Γ .ground → Program (.ground::Γ) → Program Γ
  | unary {Γ} : Input [] (.arrow .ground .ground) → Variable Γ .ground → Program (.ground::Γ) → Program Γ
noncomputable def Eval {Γ} (ρ : Variable Γ .ground → Nat) : Program Γ → Prop
  | .matrix d a root => BooleanWire.evaluate d (fun i => (a i).value (ExistentialPlan.inputs ρ)) root=true
  | .add a b q => Eval (ExistentialPlan.extend ρ (a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ))) q
  | .literal k q => Eval (ExistentialPlan.extend ρ k) q
  | .observation t q => Eval (ExistentialPlan.extend ρ (sourceValue ρ t)) q
  | .unary h x q => Eval (ExistentialPlan.extend ρ (sourceValue ρ (call h x))) q

def lower {Γ} : Program Γ → ExistentialPlan.Plan Γ
  | .matrix d a root => BooleanPlan.matrixPlan d a root
  | .add a b q => .existsGround (.gate
      (.add (ExistentialPlan.portRename (Renaming.weaken Γ .ground) a)
        (ExistentialPlan.portRename (Renaming.weaken Γ .ground) b) (.var .here)) (lower q))
  | .literal k q => BinaryPlan.constantPlan k (lower q)
  | .observation t q => .existsGround (.equation
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t) (ScopedDAG.variableInput .here) (lower q))
  | .unary h x q => .existsGround (.equation
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) (call h x)) (ScopedDAG.variableInput .here) (lower q))

/-- Reference/Boolean/arithmetic node and binary-literal budget. Source tables
may be shared externally across calls: only their MAXIMUM size is used below,
so repeated occurrences are paid by a polynomial, not silently assumed free. -/
def Program.codeSize {Γ} : Program Γ → Nat
  | .matrix (n:=n) (m:=m) _ _ _ => n+m+1
  | .add _ _ q | .observation _ q => 1+q.codeSize
  | .literal k q => Nat.log2 k+2+q.codeSize
  | .unary _ _ q => 3+q.codeSize
def Program.sourceMax {Γ} : Program Γ → Nat
  | .matrix _ _ _ => 0
  | .add _ _ q | .literal _ q => q.sourceMax
  | .observation t q => max t.specs.length q.sourceMax
  | .unary h _ q => max h.specs.length q.sourceMax
def Program.load {Γ} : Program Γ → Nat
  | .matrix (n:=n) (m:=m) _ _ _ => n+m+1
  | .add _ _ q => 1+q.load
  | .literal k q => Nat.log2 k+2+q.load
  | .observation t q => t.specs.length+1+q.load
  | .unary h _ q => h.specs.length+3+q.load

def strictPair {Γ} (p : Program Γ) := ExistentialPlan.strictPair (lower p)
def weakPair {Γ} (p : Program Γ) := ExistentialPlan.weakPair (lower p)
def budget {Γ} (p : Program Γ) : Nat := 10000*p.codeSize*(p.sourceMax+1)+7
end LogicLineages.OrdinalComparison.Source.BooleanCompiler
