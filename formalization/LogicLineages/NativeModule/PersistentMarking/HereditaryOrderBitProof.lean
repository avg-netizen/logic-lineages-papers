module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryDecodedValiditySupport
public import LogicLineages.NativeModule.PersistentMarking.HereditaryOrderTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryOrderBitProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def bits (E : Environment) (σ : Ty) (Δ : Context) : List Kind :=
  [Kind.available] ++ (distinctObservations (DecisionObservations.observations E.names E.ports Δ E.target σ)).map Kind.weak ++
  (distinctObservations (DecisionObservations.observations E.names E.ports Δ E.target σ)).map Kind.strict

def bit (v : Value) (Δ : Context) : Kind → Bool
  | .available => v.available Δ
  | .weak t => v.weak Δ t
  | .strict t => v.strict Δ t
  | .application _ _ _ => false

theorem membership (E : Environment) (σ : Ty) (Γ Δ : Context)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) (k : Kind) (hk : k ∈ bits E σ Δ) :
    (⟨Δ,k⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
  apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ _ _).mpr
  refine ⟨Δ,hw,he,rfl,?_⟩
  simp only [bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hk
  rcases hk with (hk|hk)|hk
  · exact Or.inl ⟨hk,rfl⟩
  · obtain ⟨t,ht,rfl⟩ := hk
    exact Or.inr (Or.inl ⟨t,((FiniteEqualityProof.observations _).1 t).mp ht,rfl,rfl⟩)
  · obtain ⟨t,ht,rfl⟩ := hk
    exact Or.inr (Or.inr (Or.inl ⟨t,((FiniteEqualityProof.observations _).1 t).mp ht,rfl,rfl⟩))

theorem bitLookup (E : Environment) (σ : Ty) (Γ Δ : Context) (c : Code) (k : Kind) (i : Nat)
    (hk : k ∈ bits E σ Δ) (hi : lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,k⟩ = some i) :
    bit (HereditaryDomainSemantics.decode E σ Γ c) Δ k = (i == 1) := by
  simp only [bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hk
  rcases hk with (hk|hk)|hk
  · cases hk; simp only [bit,HereditaryDomainSemantics.decode,hi,Option.getD_some]
  · obtain ⟨t,ht,rfl⟩ := hk
    simp only [bit,HereditaryDomainSemantics.decode,hi,Option.getD_some]
  · obtain ⟨t,ht,rfl⟩ := hk
    simp only [bit,HereditaryDomainSemantics.decode,hi,Option.getD_some]

theorem smallOrder (i j : Nat) (hi : i<2) (hj : j<2) :
    (decide (i≤j) = true ↔ ((i==1)=true → (j==1)=true)) := by
  have h : i=0 ∨ i=1 := by omega
  have k : j=0 ∨ j=1 := by omega
  rcases h with rfl|rfl <;> rcases k with rfl|rfl <;> decide

theorem localExact (E : Environment) (σ : Ty) (Γ Δ : Context) (a b : Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ha : a ∈ (descriptor E σ).carriers Γ) (hb : b ∈ (descriptor E σ).carriers Γ) (k : Kind)
    (hk : k ∈ bits E σ Δ) :
    ((match lookup (layout E σ (canonicalLower E σ) Γ) a ⟨Δ,k⟩,
      lookup (layout E σ (canonicalLower E σ) Γ) b ⟨Δ,k⟩ with
      | some i,some j => decide (i≤j) | _,_ => false) = true ↔
      (bit (HereditaryDomainSemantics.decode E σ Γ a) Δ k = true →
       bit (HereditaryDomainSemantics.decode E σ Γ b) Δ k = true)) := by
  have hm := membership E σ Γ Δ hw he k hk
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ
  obtain ⟨i,hi,hib⟩ := HereditaryCoordinateBoundsProof.lookupCoordinate _ a _ 2 hd
    ((HereditaryConstructionProof.effective E σ Γ a).mp ha).1 hm
  obtain ⟨j,hj,hjb⟩ := HereditaryCoordinateBoundsProof.lookupCoordinate _ b _ 2 hd
    ((HereditaryConstructionProof.effective E σ Γ b).mp hb).1 hm
  change lookup (layout E σ (canonicalLower E σ) Γ) a ⟨Δ,k⟩ = some i at hi
  change lookup (layout E σ (canonicalLower E σ) Γ) b ⟨Δ,k⟩ = some j at hj
  rw [hi,hj,bitLookup E σ Γ Δ a k i hk hi,bitLookup E σ Γ Δ b k j hk hj]
  exact smallOrder i j hib hjb

theorem bitsExact (E : Environment) (σ : Ty) (Δ : Context) (a b : Value) :
    (∀ k, k ∈ bits E σ Δ → (bit a Δ k = true → bit b Δ k = true)) ↔
    (a.available Δ = true → b.available Δ = true) ∧
    (∀ t, t ∈ DecisionObservations.observations E.names E.ports Δ E.target σ →
      (a.weak Δ t = true → b.weak Δ t = true) ∧ (a.strict Δ t = true → b.strict Δ t = true)) := by
  constructor
  · intro h
    constructor
    · exact h .available (by simp [bits])
    · intro t ht
      have hm := ((FiniteEqualityProof.observations _).1 t).mpr ht
      exact ⟨h (.weak t) (by simp [bits,hm]),h (.strict t) (by simp [bits,hm])⟩
  · rintro ⟨ha,ho⟩ k hk
    simp only [bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hk
    rcases hk with (hk|hk)|hk
    · cases hk; exact ha
    · obtain ⟨t,ht,rfl⟩ := hk
      exact (ho t (((FiniteEqualityProof.observations _).1 t).mp ht)).1
    · obtain ⟨t,ht,rfl⟩ := hk
      exact (ho t (((FiniteEqualityProof.observations _).1 t).mp ht)).2

end LogicLineages.PersistentMarking.HereditaryOrderBitProof
