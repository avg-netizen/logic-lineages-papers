module
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraphTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayer
open ComputableRankedProof (mapGraph)
open PolicyIndexedRankedGraph (Matrix Layer LiteralLayer)

abbrev Assembly (A β σ : Type) := A → β × List σ → Part (Option σ)
abbrev State (β σ : Type) := List β × Matrix β σ

variable {A β σ : Type} [Primcodable β]

/-- Pop the next original node, run the actual indexed assembler with
ordered child lookups on the previous layer, and append its optional row. -/
noncomputable def advance (l : β → List β) (assemble : Assembly A β σ)
    (a : A) (prev : Matrix β σ) (s : State β σ) : Part (State β σ) :=
  match s.1 with
  | [] => Part.some s
  | b :: bs => (assemble a (b,mapGraph prev (l b))).map (fun out =>
      (bs,s.2 ++ (out.map (b, ·)).toList))

noncomputable def passes (l : β → List β) (assemble : Assembly A β σ)
    (a : A) (prev : Matrix β σ) (s : State β σ) : Nat → Part (State β σ)
  | 0 => Part.some s
  | i+1 => (passes l assemble a prev s i).bind (advance l assemble a prev)

noncomputable def layer (l : β → List β) (assemble : Assembly A β σ) : Layer A β σ :=
  fun a (nodes,prev) => (passes l assemble a prev (nodes,[]) nodes.length).map Prod.snd

def ExactIndexedLayer : Prop :=
  ∀ (A β σ : Type) [Primcodable β]
    (l : β → List β) (assemble : Assembly A β σ) (a : A) (g : β → List σ → Option σ),
    (∀ (b : β) (vals : List σ), assemble a (b,vals) = Part.some (g b vals)) →
    LiteralLayer l (layer l assemble) a g

def IndexedLayerEffectivity : Prop :=
  ∀ (A β σ : Type) [Primcodable A] [Primcodable β] [Primcodable σ]
    (l : β → List β) (assemble : Assembly A β σ),
    Primrec l → Partrec₂ assemble → Partrec₂ (layer l assemble)

def FullPolicyIndexedRankedLayer : Prop := ExactIndexedLayer ∧ IndexedLayerEffectivity

end LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayer
