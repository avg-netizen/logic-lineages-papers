module
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.Targets
open PrimitiveLowering BooleanFlatten

def FlattenExact : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (w : Fin m → Port Γ) (z : Fin m → Fin 8 → Port Γ)
    (one : Port Γ) (ρ : OrdinalComponent Γ → Nat), one.value ρ = 1 →
  ((∀ g ∈ flatten d a w z one, g.Holds ρ) ↔
    BooleanWire.Holds d (fun i => (a i).value ρ) (fun i => (w i).value ρ)
      (fun i j => (z i j).value ρ))

/-- Old components, including higher-type coordinates, preserve identity;
all freshly addressed bit/aux/constant slots read the SAME global valuation. -/
def SharedInputs : Prop := ∀ (Γ : List Ty) (m : Nat) (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat),
  (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
    extend ρ (9*m+1) v ⟨τ,shift (9*m+1) x,j⟩ = ρ ⟨τ,x,j⟩) ∧
  (∀ i : Fin m, (bitPort (Γ:=Γ) i).value (extend ρ (9*m+1) v) = v (bitIndex i)) ∧
  (∀ (i : Fin m) (j : Fin 8), (auxPort (Γ:=Γ) i j).value (extend ρ (9*m+1) v) = v (auxIndex i j)) ∧
  (onePort (Γ:=Γ) m).value (extend ρ (9*m+1) v) = v (oneIndex m)

def GlobalExact : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (root : Fin m) (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat),
  Holds d a root ρ v ↔
    v (oneIndex m) = 1 ∧
    BooleanWire.Holds d (fun i => (a i).value ρ) (fun i => v (bitIndex i))
      (fun i j => v (auxIndex i j)) ∧ v (bitIndex root) = 1

def ExistentialExact : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (root : Fin m) (ρ : OrdinalComponent Γ → Nat),
  (∃ v : Fin (9*m+1) → Nat, Holds d a root ρ v) ↔
    BooleanWire.evaluate d (fun i => (a i).value ρ) root = true

/-- Actual literal gate-list length, not a count of hypothetical constraints.
This is a Boolean-to-arithmetic supplier, NOT the whole source compiler. -/
def LinearOverhead : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (root : Fin m),
  (compile d a root).length = BooleanWire.atomCount d + 2 ∧
  (compile d a root).length ≤ 9*m+2 ∧ (Global Γ m).length = 9*m+1+Γ.length
end LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.Targets
