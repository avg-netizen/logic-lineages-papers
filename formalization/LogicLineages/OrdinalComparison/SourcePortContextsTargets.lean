module
public import LogicLineages.OrdinalComparison.SourcePortContextsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePortContextsTargets
open SourceTypedPorts SourceFreeOccurrences SourcePortContexts

def PortContextEnumeration : Prop := ∀ (B : Nat) (K : List Ty) (P : PortContext B),
    P ∈ portContexts B K ↔ ValidPorts K.toFinset P

def ValidPortLength : Prop := ∀ (B : Nat) (K : Finset Ty) (P : PortContext B),
    ValidPorts K P → P.length ≤ B

def TypedAssignmentInjective : Prop := ∀ (Γ Θ Λ : List Ty) (a : PortMap Θ Λ),
    (indices a).Nodup → Function.Injective
      (fun v : PackedVariable Λ => (⟨v.1, renameWith Γ a (embedLeft Γ v.2)⟩ : PackedVariable (Θ ++ Γ)))

def ExternalPortAssignment : Prop := ∀ (B : Nat) (K : Finset Ty) (P : PortContext B)
    (Λ : List Ty) (a : PortMap (portTypes P) Λ), ValidPorts K P → (indices a).Nodup →
    (∀ v : PackedVariable Λ, ∃ i : Fin B, assignedPortId P a v = some i) ∧
    Function.Injective (assignedPortId P a)

def FreshPortExtension : Prop := ∀ (B : Nat) (K : Finset Ty) (P : PortContext B)
    (i : Fin B) (σ : Ty), ValidPorts K P → i ∉ P.map Prod.fst → σ ∈ K →
    ValidPorts K ((i, σ) :: P) ∧ portTypes ((i, σ) :: P) = σ :: portTypes P ∧
    ((i, σ) :: P).length = P.length + 1
def LiteralTypeEnumeration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ),
    (literalTypes t).toFinset = SourceTypeSupport.typeSupport t
end LogicLineages.OrdinalComparison.Source.SourcePortContextsTargets
