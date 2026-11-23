module
public import LogicLineages.StandardControlCurrent.ComputableRankedProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraph
open ComputableRankedProof (bindList mapGraph)

abbrev Matrix (β σ : Type) := List (β × σ)
abbrev Layer (A β σ : Type) := A → List β × Matrix β σ → Part (Matrix β σ)

variable {A β σ : Type} [Primcodable β]

/-- The shared index stays unchanged; each pass receives the original
ranked frontier and the completed previous level. -/
noncomputable def sweep (m : β → Nat) (l : β → List β) (layer : Layer A β σ)
    (a : A) (root : β) : Nat → Part (Matrix β σ)
  | 0 => Part.some []
  | i+1 => (sweep m l layer a root i).bind fun prev =>
      layer a (bindList l root (m root-i),prev)

noncomputable def root (m : β → Nat) (l : β → List β) (layer : Layer A β σ)
    (p : A × β) : Part (Option σ) :=
  (sweep m l layer p.1 p.2 (m p.2+1)).map (fun tab => tab[0]?.map Prod.snd)

/-- The original option can omit a row, distinct from a diverging layer. -/
def LiteralLayer (l : β → List β) (layer : Layer A β σ) (a : A)
    (g : β → List σ → Option σ) : Prop :=
  ∀ (nodes : List β) (prev : Matrix β σ),
    layer a (nodes,prev) = Part.some (nodes.filterMap fun b =>
      (g b (mapGraph prev (l b))).map (b, ·))

def ExactPolicyIndexedRankedGraph : Prop :=
  ∀ (A β σ : Type) [Primcodable β]
    (m : β → Nat) (l : β → List β) (layer : Layer A β σ)
    (a : A) (g : β → List σ → Option σ), LiteralLayer l layer a g →
    (∀ (b : β) (i : Nat), sweep m l layer a b i =
      Part.some (ComputableRankedProof.graph m l g b i)) ∧
    ∀ b : β, root m l layer (a,b) =
      Part.some ((ComputableRankedProof.graph m l g b (m b+1))[0]?.map Prod.snd)

def PolicyIndexedRankedEffectivity : Prop :=
  ∀ (A β σ : Type) [Primcodable A] [Primcodable β] [Primcodable σ]
    (m : β → Nat) (l : β → List β) (layer : Layer A β σ),
    Primrec m → Primrec l → Partrec₂ layer →
    Partrec (fun p : (A × β) × Nat => sweep m l layer p.1.1 p.1.2 p.2) ∧
    Partrec (root m l layer)

def FullPolicyIndexedRankedGraph : Prop :=
  ExactPolicyIndexedRankedGraph ∧ PolicyIndexedRankedEffectivity

end LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraph
