module
public import LogicLineages.OrdinalComparison.SourceBooleanWireDefinitions
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanFlatten
open PrimitiveLowering

/-- Every reference is translated into the SAME global typed context. -/
def refPort {Γ n m} (a : Fin n → Port Γ) (w : Fin m → Port Γ)
    (b : Port Γ) (z : Fin 8 → Port Γ) (one : Port Γ) : BooleanWire.Ref n m → Port Γ
  | .input i => a i
  | .previous i => w i
  | .output => b
  | .aux i => z i
  | .zero => .zero
  | .one => one

def atomGate {Γ n m} (a : Fin n → Port Γ) (w : Fin m → Port Γ)
    (b : Port Γ) (z : Fin 8 → Port Γ) (one : Port Γ) : BooleanWire.Atom n m → Gate Γ
  | .eq x y => .eq (refPort a w b z one x) (refPort a w b z one y)
  | .add x y v => .add (refPort a w b z one x) (refPort a w b z one y) (refPort a w b z one v)
  | .sort x y l h => .sort (refPort a w b z one x) (refPort a w b z one y)
      (refPort a w b z one l) (refPort a w b z one h)

/-- Flattening retains sharing: a predecessor is an address, never a copy
of its producing graph. There is no arbitrary relation or predicate oracle. -/
def flatten {Γ n} : {m : Nat} → BooleanWire.Dag n m → (Fin n → Port Γ) →
    (Fin m → Port Γ) → (Fin m → Fin 8 → Port Γ) → Port Γ → List (Gate Γ)
  | _, .nil, _, _, _, _ => []
  | _, .snoc d g, a, w, z, one =>
      flatten d a (fun i => w i.succ) (fun i => z i.succ) one ++
        (BooleanWire.constraints g).map (atomGate a (fun i => w i.succ) (w 0) (z 0) one)

abbrev Global (Γ : List Ty) (m : Nat) := List.replicate (9*m+1) Ty.ground ++ Γ

def bitIndex {m} (i : Fin m) : Fin (9*m+1) := ⟨9*i.val, by omega⟩
def auxIndex {m} (i : Fin m) (j : Fin 8) : Fin (9*m+1) := ⟨9*i.val+j.val+1, by omega⟩
def oneIndex (m : Nat) : Fin (9*m+1) := ⟨9*m, by omega⟩

def inputPort {Γ} (m : Nat) : Port Γ → Port (Global Γ m)
  | .zero => .zero
  | .var x => .var (shift (9*m+1) x)
def bitPort {Γ m} (i : Fin m) : Port (Global Γ m) := .var (fresh (bitIndex i))
def auxPort {Γ m} (i : Fin m) (j : Fin 8) : Port (Global Γ m) := .var (fresh (auxIndex i j))
def onePort {Γ} (m : Nat) : Port (Global Γ m) := .var (fresh (oneIndex m))

/-- One common constant-one wire, followed by all node constraints and a
root assertion. The original typed context is untouched behind the prefix. -/
def compile {Γ n m} (d : BooleanWire.Dag n m) (a : Fin n → Port Γ) (root : Fin m) :
    List (Gate (Global Γ m)) :=
  .one (onePort m) :: (flatten d (fun i => inputPort m (a i)) bitPort auxPort (onePort m) ++
    [.eq (bitPort root) (onePort m)])

def Holds {Γ n m} (d : BooleanWire.Dag n m) (a : Fin n → Port Γ) (root : Fin m)
    (ρ : OrdinalComponent Γ → Nat) (v : Fin (9*m+1) → Nat) : Prop :=
  ∀ g ∈ compile d a root, g.Holds (extend ρ (9*m+1) v)

/-- Explicit packing of the existing bit/aux witnesses; the only last slot
is the common constant one. Quotient/remainder decode fixed-size blocks. -/
def pack {m} (w : Fin m → Nat) (z : Fin m → Fin 8 → Nat) : Fin (9*m+1) → Nat :=
  fun i => if h : i.val < 9*m then
    if h0 : i.val % 9 = 0 then w ⟨i.val/9, by omega⟩
    else z ⟨i.val/9, by omega⟩ ⟨i.val%9-1, by omega⟩
  else 1
end LogicLineages.OrdinalComparison.Source.BooleanFlatten
