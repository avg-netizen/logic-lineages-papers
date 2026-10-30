module
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesDefinitions
@[expose] public section
/-! Finite positional typed assignments, distinct from the external Fin B port
identifiers. All variable/map enumeration is literal finite recursion. -/
namespace LogicLineages.OrdinalComparison.Source.SourceTypedPorts

def variableIndex : {Γ : List Ty} → {σ : Ty} → Variable Γ σ → Nat
  | _, _, .here => 0
  | _, _, .there v => variableIndex v + 1

def enumerateVariables : (Γ : List Ty) → (σ : Ty) → List (Variable Γ σ)
  | [], _ => []
  | τ :: Γ, σ =>
      (if h : τ = σ then [Eq.mp (congrArg (Variable (τ :: Γ)) h) Variable.here] else []) ++
      (enumerateVariables Γ σ).map Variable.there

inductive PortMap (Θ : List Ty) : List Ty → Type where
  | nil : PortMap Θ []
  | cons {σ : Ty} {Λ : List Ty} : Variable Θ σ → PortMap Θ Λ → PortMap Θ (σ :: Λ)

def indices {Θ Λ : List Ty} : PortMap Θ Λ → List Nat
  | .nil => []
  | .cons v rest => variableIndex v :: indices rest

def allMaps (Θ : List Ty) : (Λ : List Ty) → List (PortMap Θ Λ)
  | [] => [.nil]
  | σ :: Λ => (enumerateVariables Θ σ).flatMap fun v => (allMaps Θ Λ).map (PortMap.cons v)

def injectiveMaps (Θ Λ : List Ty) : List (PortMap Θ Λ) :=
  (allMaps Θ Λ).filter fun a => decide (indices a).Nodup

def embedLeft (Γ : List Ty) : {Θ : List Ty} → {σ : Ty} → Variable Θ σ → Variable (Θ ++ Γ) σ
  | _, _, .here => .here
  | _, _, .there v => .there (embedLeft Γ v)

def shiftVariable (Θ : List Ty) {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) : Variable (Θ ++ Γ) σ :=
  match Θ with
  | [] => v
  | _ :: Θ => .there (shiftVariable Θ v)

def renameWith (Γ : List Ty) {Θ Λ : List Ty} (a : PortMap Θ Λ) :
    Renaming (Λ ++ Γ) (Θ ++ Γ) :=
  match a with
  | .nil => fun v => shiftVariable Θ v
  | .cons v rest => fun w => match w with
      | .here => embedLeft Γ v
      | .there w => renameWith Γ rest w

def shiftMap (σ : Ty) {Θ Λ : List Ty} : PortMap Θ Λ → PortMap (σ :: Θ) Λ
  | .nil => .nil
  | .cons v rest => .cons (.there v) (shiftMap σ rest)

def liftMap (σ : Ty) {Θ Λ : List Ty} (a : PortMap Θ Λ) : PortMap (σ :: Θ) (σ :: Λ) :=
  .cons .here (shiftMap σ a)

end LogicLineages.OrdinalComparison.Source.SourceTypedPorts
