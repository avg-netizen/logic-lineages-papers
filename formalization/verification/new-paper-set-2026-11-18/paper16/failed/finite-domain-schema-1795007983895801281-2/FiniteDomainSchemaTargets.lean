import LogicLineages.PersistentMarking.FiniteDomainSchema
namespace LogicLineages.PersistentMarking.FiniteDomainSchemaTargets
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema

def ExtensionTest : Prop := ∀ Γ Δ, extendsBool Γ Δ = true ↔ Extends Γ Δ
def ExtensionEnumeration : Prop := ∀ K B Γ Δ,
  Δ ∈ extensions K B Γ ↔ WellFormed K B Δ ∧ Extends Γ Δ
def ExtensionDistinct : Prop := ∀ K B Γ, (extensions K B Γ).Pairwise (· ≠ ·)
def LocalSchemaExact : Prop := ∀ σ (lower : LowerCarrier σ) V B target Δ key bound,
  (key,bound) ∈ atContext σ lower V B target Δ ↔ AtContextSpec σ lower V B target Δ key bound
def SchemaExact : Prop := ∀ σ (lower : LowerCarrier σ) K V B target Γ key bound,
  (key,bound) ∈ schema σ lower K V B target Γ ↔ CoordinateSpec σ lower K V B target Γ key bound
def SchemaKeysDistinct : Prop := ∀ σ (lower : LowerCarrier σ) K V B target Γ,
  ((schema σ lower K V B target Γ).map Prod.fst).Pairwise (· ≠ ·)
def RestrictionKeys : Prop := ∀ σ (lower : LowerCarrier σ) K V B target Γ Θ,
  Extends Γ Θ → ∀ key bound, (key,bound) ∈ schema σ lower K V B target Θ →
    (key,bound) ∈ schema σ lower K V B target Γ

def RawCodeExact : Prop := ∀ σ (lower : LowerCarrier σ) K V B target Γ code,
  code ∈ rawCodes σ lower K V B target Γ ↔
    Fits ((schema σ lower K V B target Γ).map Prod.snd) code
def RawCodeDistinct : Prop := ∀ σ (lower : LowerCarrier σ) K V B target Γ,
  (rawCodes σ lower K V B target Γ).Pairwise (· ≠ ·)

def ArgumentBoundCoordinates : Prop := ∀ σ (lower : LowerCarrier σ) Δ domains τ
  (h : (domains,τ) ∈ fullPrefixes σ),
  (argumentBounds σ lower Δ domains τ h).length = domains.length ∧
  ∀ (i : Nat) (ρ : Ty) (hi : domains[i]? = some ρ),
    ∃ hp : typeSize ρ < typeSize σ,
      (argumentBounds σ lower Δ domains τ h)[i]? = some (lower ρ hp Δ).length
end LogicLineages.PersistentMarking.FiniteDomainSchemaTargets
