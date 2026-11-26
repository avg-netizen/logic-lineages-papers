import LogicLineages.PersistentMarking.HereditaryOutputProof
namespace LogicLineages.PersistentMarking.HereditaryEncodeCoordinateProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

/- Proof-local spelling of the actual encoder coordinate; equality below is
by reflexivity, with no changed retention or decoding convention. -/
def coordinate (E : Environment) (v : Value) (kb : Key × Nat) : Nat :=
  let Δ := kb.1.context
  match kb.1.kind with
  | .available => if v.available Δ then 1 else 0
  | .weak t => if v.weak Δ t then 1 else 0
  | .strict t => if v.strict Δ t then 1 else 0
  | .application ds τ is =>
    ((do
      let xs ← HereditaryDomainSemantics.values E Δ ds is
      indexOf ((descriptor E τ).carriers Δ) (v.application Δ ds τ xs)) : Option Nat).getD 0

theorem encodeMap (E : Environment) (σ : Ty) (Γ : Context) (v : Value) :
    encode E σ Γ v = (layout E σ (canonicalLower E σ) Γ).map (coordinate E v) := rfl

theorem lookupEncoded (E : Environment) (σ : Ty) (Γ : Context) (v : Value) (key : Key) (bound : Nat)
    (hm : (key,bound) ∈ layout E σ (canonicalLower E σ) Γ) :
    lookup (layout E σ (canonicalLower E σ) Γ) (encode E σ Γ v) key =
      some (coordinate E v (key,bound)) := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ
  apply HereditaryLookupProof.lookupAt _ _ i key bound _ hd hi
  rw [encodeMap]
  simp only [List.getElem?_map,hi,Option.map_some]

theorem bitRoundtrip (i : Nat) (hi : i < 2) : (if i == 1 then 1 else 0) = i := by
  have h : i=0 ∨ i=1 := by omega
  rcases h with rfl|rfl <;> rfl

end LogicLineages.PersistentMarking.HereditaryEncodeCoordinateProof
