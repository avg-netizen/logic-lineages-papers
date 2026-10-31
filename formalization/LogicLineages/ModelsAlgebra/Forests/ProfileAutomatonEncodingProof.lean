module
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingTargets
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.Proof
open RankedParse FiniteProfile RankedGraphImage

theorem familyBoundCorrect : Targets.FamilyBoundCorrect := by
  intro F
  induction F with
  | nil => intro A h; cases h
  | cons B F ih =>
    intro A h
    rcases List.mem_cons.mp h with h | h
    · subst A
      exact Nat.le_max_left _ _
    · exact (ih A h).trans (Nat.le_max_right _ _)

def encodeVertex (N : Nat) (A : RawGraph) (h : A.1 ≤ N) (x : Fin A.1) :
    Vertex (encode N A) :=
  ⟨⟨x.val, Nat.lt_of_lt_of_le x.isLt h⟩, by simp [encode, x.isLt]⟩

def decodeVertex (N : Nat) (A : RawGraph) (x : Vertex (encode N A)) : Fin A.1 :=
  ⟨x.val.val, of_decide_eq_true x.property⟩

def encodingEquiv (N : Nat) (A : RawGraph) (h : A.1 ≤ N) :
    Fin A.1 ≃ Vertex (encode N A) where
  toFun := encodeVertex N A h
  invFun := decodeVertex N A
  left_inv := by intro x; apply Fin.ext; rfl
  right_inv := by intro x; apply Subtype.ext; apply Fin.ext; rfl

theorem encodingIso : Targets.EncodingIso := by
  intro N A h
  refine ⟨{ toEquiv := encodingEquiv N A h, map_rel_iff' := ?_ }⟩
  intro x y
  change ((encodeVertex N A h x).val ≠ (encodeVertex N A h y).val ∧
      ((encode N A).2 (encodeVertex N A h x).val (encodeVertex N A h y).val = true ∨
       (encode N A).2 (encodeVertex N A h y).val (encodeVertex N A h x).val = true)) ↔
    (x ≠ y ∧ (A.2 x y = true ∨ A.2 y x = true))
  simp [encodeVertex, encode, x.isLt, y.isLt, Fin.ext_iff]

theorem finiteGraphRepresentability : Targets.FiniteGraphRepresentability := by
  classical
  intro G
  letI : Fintype G.Vertex := Fintype.ofFinite G.Vertex
  let e : G.Vertex ≃ Fin (Fintype.card G.Vertex) := Fintype.equivFin G.Vertex
  let A : RawGraph := ⟨Fintype.card G.Vertex,
    fun x y => decide (G.edges.Adj (e.symm x) (e.symm y))⟩
  refine ⟨A, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro x y
  change (e x ≠ e y ∧
    (decide (G.edges.Adj (e.symm (e x)) (e.symm (e y))) = true ∨
     decide (G.edges.Adj (e.symm (e y)) (e.symm (e x))) = true)) ↔ G.edges.Adj x y
  simp only [Equiv.symm_apply_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact G.edges.adj_symm h
  · intro h
    exact ⟨fun he => G.edges.ne_of_adj h (e.injective he), Or.inl h⟩

theorem machineRun_eq (F : List RawGraph) (t : Term) :
    machineRun (machine F) t = FiniteProfile.run (familyBound F) t := by
  induction t with
  | atom => rfl
  | node o l r ihl ihr =>
    change transition o (machineRun (machine F) l) (machineRun (machine F) r) =
      transition o (FiniteProfile.run (familyBound F) l) (FiniteProfile.run (familyBound F) r)
    rw [ihl, ihr]

theorem encodedProfile (N : Nat) (A : RawGraph) (h : A.1 ≤ N) (t : Term) :
    Profile (encode N A) t ↔ Nonempty (rawGraph A ↪g graph t) := by
  obtain ⟨e⟩ := encodingIso N A h
  constructor
  · rintro ⟨f⟩
    exact ⟨f.comp e.toEmbedding⟩
  · rintro ⟨f⟩
    exact ⟨f.comp e.symm.toEmbedding⟩

theorem machineCorrect : Targets.MachineCorrect := by
  intro F t
  rw [machineRun_eq]
  change decide (Accepts (encodedFamily F) (FiniteProfile.run (familyBound F) t)) = true ↔ _
  rw [decide_eq_true_eq, FiniteProfile.Proof.acceptanceExact (familyBound F) (encodedFamily F) t]
  constructor
  · intro h A hA he
    exact h (encode (familyBound F) A) (List.mem_map.mpr ⟨A, hA, rfl⟩)
      ((encodedProfile (familyBound F) A (familyBoundCorrect F A hA) t).mpr he)
  · intro h C hC hp
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact h A hA ((encodedProfile (familyBound F) A (familyBoundCorrect F A hA) t).mp hp)

theorem rawAvoidanceDownward : Targets.RawAvoidanceDownward := by
  intro F s t hst ht A hA hs
  obtain ⟨f⟩ := hs
  obtain ⟨g⟩ := RankedParse.Proof.homeomorphicInduced s t hst
  exact ht A hA ⟨(RankedParse.Proof.asGraphEmbedding g).comp f⟩

theorem arbitraryFiniteFamilyRegular : Targets.ArbitraryFiniteFamilyRegular := by
  classical
  intro Gs
  let code : FiniteGraph → RawGraph := fun G => Classical.choose (finiteGraphRepresentability G)
  let iso (G : FiniteGraph) : G.edges ≃g rawGraph (code G) :=
    Classical.choice (Classical.choose_spec (finiteGraphRepresentability G))
  refine ⟨Gs.map code, ?_⟩
  intro t
  rw [machineCorrect]
  constructor
  · intro h G hG he
    obtain ⟨e⟩ := he
    exact h (code G) (List.mem_map.mpr ⟨G, hG, rfl⟩) ⟨e.comp (iso G).symm.toEmbedding⟩
  · intro h A hA he
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hA
    obtain ⟨e⟩ := he
    exact h G hG ⟨e.comp (iso G).toEmbedding⟩

end LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.Proof
