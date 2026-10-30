module
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePortContexts
open SourceTypedPorts SourceFreeOccurrences

abbrev PortContext (B : Nat) := List (Fin B × Ty)
def portTypes {B : Nat} (P : PortContext B) : List Ty := P.map Prod.snd

def ValidPorts {B : Nat} (K : Finset Ty) (P : PortContext B) : Prop :=
  (P.map Prod.fst).Nodup ∧ ∀ p ∈ P, p.2 ∈ K

def listsOfLength {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun x => (listsOfLength alphabet n).map (List.cons x)

def portContexts (B : Nat) (K : List Ty) : List (PortContext B) :=
  ((List.range (B + 1)).flatMap fun n =>
    listsOfLength ((List.finRange B).product K) n).filter
      (fun P => decide (P.map Prod.fst).Nodup)

/-- Executable literal type support listing, retaining harmless duplicates. -/
def literalTypes {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : List Ty :=
  τ.subtypes ++ match t with
  | .var _ | .zeroC | .succC | .caseC _ | .recC _ => []
  | .app f a => literalTypes f ++ literalTypes a
  | .lam body => literalTypes body
  | .ranked s args => (List.ofFn fun i : Fin (arity s) => literalTypes (args i)).flatten

def assignedPortId {B : Nat} (P : PortContext B) {Λ : List Ty}
    (a : PortMap (portTypes P) Λ) (v : PackedVariable Λ) : Option (Fin B) :=
  (P.map Prod.fst)[variableIndex (renameWith [] a (embedLeft [] v.2))]?

end LogicLineages.OrdinalComparison.Source.SourcePortContexts
