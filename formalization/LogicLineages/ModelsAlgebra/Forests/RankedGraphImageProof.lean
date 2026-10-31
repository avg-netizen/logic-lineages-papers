module
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedParseProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.Proof
open RankedParse

theorem pruneGraphEmbedding : Targets.PruneGraphEmbedding := by
  classical
  intro V _ G t f
  have hb : ∃ y : Leaf t, ∃ v : V, f v = y := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨f v, v, rfl⟩
  obtain ⟨s, hs, q, hq⟩ := RankedParse.Proof.exactPruning t
    (fun y => ∃ v : V, f v = y) hb
  let e : Leaf s → V := fun x => Classical.choose ((hq (q.map x)).mp ⟨x, rfl⟩)
  have he : ∀ x, f (e x) = q.map x :=
    fun x => Classical.choose_spec ((hq (q.map x)).mp ⟨x, rfl⟩)
  have hei : Function.Injective e := by
    intro x y h
    apply q.injective
    rw [← he x, ← he y, h]
  have hes : Function.Surjective e := by
    intro v
    obtain ⟨x, hx⟩ := (hq (f v)).mpr ⟨v, rfl⟩
    exact ⟨x, f.injective ((he x).trans hx)⟩
  let iso : graph s ≃g G := {
    toEquiv := Equiv.ofBijective e ⟨hei, hes⟩
    map_rel_iff' := by
      intro x y
      change G.Adj (e x) (e y) ↔ Adj s x y
      calc
        G.Adj (e x) (e y) ↔ (graph t).Adj (f (e x)) (f (e y)) :=
          f.map_rel_iff.symm
        _ ↔ Adj s x y := by
          change Adj t (f (e x)) (f (e y)) ↔ Adj s x y
          rw [he x, he y]
          exact q.adjacency x y }
  exact ⟨s, hs, ⟨iso.symm⟩⟩

def emptyEmbedding (G H : FiniteGraph) (h : IsEmpty G.Vertex) : G.edges ↪g H.edges where
  toFun := fun v => False.elim (h.false v)
  inj' := by
    intro v w _
    exact False.elim (h.false v)
  map_rel_iff' := by
    intro v w
    exact False.elim (h.false v)

theorem embedsRefl (G : FiniteGraph) : Embeds G G :=
  ⟨SimpleGraph.Embedding.refl⟩

theorem embedsTrans (G H W : FiniteGraph) (f : Embeds G H) (g : Embeds H W) :
    Embeds G W := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact ⟨g.comp f⟩

theorem idealImage : Targets.IdealImage := by
  classical
  intro I hI
  constructor
  · intro G H hGH hH
    obtain ⟨f⟩ := hGH
    rcases hH with he | ⟨t, ht, ⟨e⟩⟩
    · exact Or.inl ⟨fun v => he.false (f v)⟩
    · by_cases he : IsEmpty G.Vertex
      · exact Or.inl he
      · letI : Nonempty G.Vertex := not_isEmpty_iff.mp he
        obtain ⟨s, hs, iso⟩ := pruneGraphEmbedding G.Vertex G.edges t (e.toEmbedding.comp f)
        exact Or.inr ⟨s, hI.downward s t hs ht, iso⟩
  · intro G H hG hH
    rcases hG with heG | ⟨s, hs, ⟨eG⟩⟩
    · exact ⟨H, hH, ⟨emptyEmbedding G H heG⟩, embedsRefl H⟩
    · rcases hH with heH | ⟨t, ht, ⟨eH⟩⟩
      · exact ⟨G, Or.inr ⟨s, hs, ⟨eG⟩⟩, embedsRefl G, ⟨emptyEmbedding H G heH⟩⟩
      · obtain ⟨u, hu, hsu, htu⟩ := hI.directed s t hs ht
        obtain ⟨f⟩ := RankedParse.Proof.homeomorphicInduced s u hsu
        obtain ⟨g⟩ := RankedParse.Proof.homeomorphicInduced t u htu
        refine ⟨evalFinite u, Or.inr ⟨u, hu, ⟨SimpleGraph.Iso.refl⟩⟩, ?_, ?_⟩
        · exact ⟨(RankedParse.Proof.asGraphEmbedding f).comp eG.toEmbedding⟩
        · exact ⟨(RankedParse.Proof.asGraphEmbedding g).comp eH.toEmbedding⟩

theorem imageCoverFromLanguage : Targets.ImageCoverFromLanguage := by
  classical
  intro ι _ I L K hL hK G
  constructor
  · intro hG
    rcases (hK G).mp hG with he | ⟨t, ht, e⟩
    · exact ⟨Classical.choice inferInstance, Or.inl he⟩
    · obtain ⟨i, hi⟩ := (hL t).mp ht
      exact ⟨i, Or.inr ⟨t, hi, e⟩⟩
  · rintro ⟨i, hi⟩
    apply (hK G).mpr
    rcases hi with he | ⟨t, ht, e⟩
    · exact Or.inl he
    · exact Or.inr ⟨t, (hL t).mpr ⟨i, ht⟩, e⟩

theorem finiteGraphHost {ι : Type} (K : FiniteGraph → Prop)
    (hjep : GraphJEP K) (a : FiniteGraph) (ha : K a) (g : ι → FiniteGraph)
    (hg : ∀ i, K (g i)) (S : Finset ι) :
    ∃ c, K c ∧ ∀ i ∈ S, Embeds (g i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨a, ha, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    obtain ⟨d, hd, hid, hcd⟩ := hjep (g i) c (hg i) hc
    refine ⟨d, hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · subst j
      exact hid
    · exact embedsTrans (g j) c d (hbound j hjS) hcd

theorem imageCover : Targets.ImageCover := by
  classical
  intro ι _ _ I K hI hcover
  have hpieces := fun i => idealImage (I i) (hI i)
  refine ⟨hpieces, ?_⟩
  constructor
  · intro hjep
    by_contra hproper
    have hmissing : ∀ i, ∃ G, K G ∧ ¬ Image (I i) G := by
      intro i
      by_contra hn
      apply hproper
      refine ⟨i, ?_⟩
      intro G
      constructor
      · intro hG
        by_contra hi
        exact hn ⟨G, hG, hi⟩
      · intro hi
        exact (hcover G).mpr ⟨i, hi⟩
    let g : ι → FiniteGraph := fun i => Classical.choose (hmissing i)
    have hg : ∀ i, K (g i) := fun i => (Classical.choose_spec (hmissing i)).1
    have hnot : ∀ i, ¬ Image (I i) (g i) :=
      fun i => (Classical.choose_spec (hmissing i)).2
    let i₀ : ι := Classical.choice inferInstance
    obtain ⟨c, hc, hbound⟩ := finiteGraphHost K hjep (g i₀) (hg i₀) g hg
      (Finset.univ : Finset ι)
    obtain ⟨j, hj⟩ := (hcover c).mp hc
    exact hnot j ((hpieces j).1 (g j) c (hbound j (Finset.mem_univ j)) hj)
  · rintro ⟨i, hi⟩ G H hG hH
    obtain ⟨W, hW, hGW, hHW⟩ := (hpieces i).2 G H ((hi G).mp hG) ((hi H).mp hH)
    exact ⟨W, (hi W).mpr hW, hGW, hHW⟩

end LogicLineages.ModelsAlgebra.Forests.RankedGraphImage.Proof
