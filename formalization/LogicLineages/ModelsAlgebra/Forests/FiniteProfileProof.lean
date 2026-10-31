module
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedParseProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteProfile.Proof
open RankedParse

def leftBase {N} {C : Code N} {P} (x : Vertex (leftCode C P)) : Vertex C :=
  ⟨x.val, (Bool.and_eq_true_iff.mp x.property).1⟩

def rightBase {N} {C : Code N} {P} (x : Vertex (rightCode C P)) : Vertex C :=
  ⟨x.val, (Bool.and_eq_true_iff.mp x.property).1⟩

theorem leftFlag {N} {C : Code N} {P} (x : Vertex (leftCode C P)) : P x.val = true :=
  (Bool.and_eq_true_iff.mp x.property).2

theorem rightFlag {N} {C : Code N} {P} (x : Vertex (rightCode C P)) : P x.val = false := by
  have h := (Bool.and_eq_true_iff.mp x.property).2
  simpa using h

def mkLeft {N} {C : Code N} {P} (x : Vertex C) (h : P x.val = true) :
    Vertex (leftCode C P) := ⟨x.val, by simp [leftCode, x.property, h]⟩

def mkRight {N} {C : Code N} {P} (x : Vertex C) (h : P x.val = false) :
    Vertex (rightCode C P) := ⟨x.val, by simp [rightCode, x.property, h]⟩

theorem leafExact : Targets.LeafExact := by
  intro N C
  constructor
  · intro h
    have hu := (Finset.mem_filter.mp h).2
    refine ⟨{ toFun := fun _ => ()
              inj' := ?_
              map_rel_iff' := ?_ }⟩
    · intro x y _
      exact Subtype.ext (hu x.val y.val x.property y.property)
    · intro x y
      change False ↔ (x.val ≠ y.val ∧ (C.2 x.val y.val = true ∨ C.2 y.val x.val = true))
      constructor
      · exact False.elim
      · intro hxy
        exact hxy.1 (hu x.val y.val x.property y.property)
  · rintro ⟨f⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ C, ?_⟩
    intro x y hx hy
    have h : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
      change (f ⟨x, hx⟩ : Unit) = f ⟨y, hy⟩
      exact @Subsingleton.elim Unit inferInstance (f ⟨x, hx⟩) (f ⟨y, hy⟩)
    exact congrArg Subtype.val (f.injective h)

def combinedMap {N} {C : Code N} {P} {l r : Term}
    (f : codeGraph (leftCode C P) ↪g graph l)
    (g : codeGraph (rightCode C P) ↪g graph r) (x : Vertex C) : Sum (Leaf l) (Leaf r) :=
  if h : P x.val = true then .inl (f (mkLeft x h))
  else .inr (g (mkRight x (Bool.eq_false_iff.mpr h)))

def combineEmbedding {N} {C : Code N} {P} {l r : Term} (o : Operation)
    (f : codeGraph (leftCode C P) ↪g graph l)
    (g : codeGraph (rightCode C P) ↪g graph r)
    (hc : Compatible o C P) : codeGraph C ↪g graph (.node o l r) where
  toFun := combinedMap f g
  inj' := by
    intro x y h
    change combinedMap f g x = combinedMap f g y at h
    by_cases hx : P x.val = true <;> by_cases hy : P y.val = true
    · have he : f (mkLeft x hx) = f (mkLeft y hy) :=
        Sum.inl.inj (by simpa only [combinedMap, dif_pos hx, dif_pos hy] using h)
      exact Subtype.ext (congrArg (fun z : Vertex (leftCode C P) => z.val) (f.injective he))
    · have he : Sum.inl (f (mkLeft x hx)) =
          Sum.inr (g (mkRight y (Bool.eq_false_iff.mpr hy))) := by
        simpa only [combinedMap, dif_pos hx, dif_neg hy] using h
      cases he
    · have he : Sum.inr (g (mkRight x (Bool.eq_false_iff.mpr hx))) =
          Sum.inl (f (mkLeft y hy)) := by
        simpa only [combinedMap, dif_neg hx, dif_pos hy] using h
      cases he
    · have he : g (mkRight x (Bool.eq_false_iff.mpr hx)) =
          g (mkRight y (Bool.eq_false_iff.mpr hy)) :=
        Sum.inr.inj (by simpa only [combinedMap, dif_neg hx, dif_neg hy] using h)
      exact Subtype.ext (congrArg (fun z : Vertex (rightCode C P) => z.val) (g.injective he))
  map_rel_iff' := by
    intro x y
    change Adj (.node o l r) (combinedMap f g x) (combinedMap f g y) ↔
      (codeGraph C).Adj x y
    by_cases hx : P x.val = true <;> by_cases hy : P y.val = true
    · simp only [combinedMap, dif_pos hx, dif_pos hy]
      exact f.map_rel_iff
    · have hn : P x.val ≠ P y.val := by rw [hx, Bool.eq_false_iff.mpr hy]; decide
      simp only [combinedMap, dif_pos hx, dif_neg hy]
      exact (hc x.val y.val x.property y.property hn).symm
    · have hn : P x.val ≠ P y.val := by rw [Bool.eq_false_iff.mpr hx, hy]; decide
      simp only [combinedMap, dif_neg hx, dif_pos hy]
      exact (hc x.val y.val x.property y.property hn).symm
    · simp only [combinedMap, dif_neg hx, dif_neg hy]
      exact g.map_rel_iff

def partition {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r)) (x : Fin N) : Bool :=
  if h : C.1 x = true then (f ⟨x, h⟩).isLeft else false

theorem partitionAt {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r)) (x : Vertex C) :
    partition f x.val = (f x).isLeft := by
  simp [partition, x.property]

def leftExtract {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r))
    (x : Vertex (leftCode C (partition f))) : Leaf l :=
  (f (leftBase x)).getLeft (by
    rw [← partitionAt f (leftBase x)]
    exact leftFlag x)

theorem leftExtractSpec {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r))
    (x : Vertex (leftCode C (partition f))) :
    f (leftBase x) = Sum.inl (leftExtract f x) := by
  exact (Sum.inl_getLeft _ _).symm

def rightExtract {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r))
    (x : Vertex (rightCode C (partition f))) : Leaf r :=
  (f (rightBase x)).getRight (by
    have h : (f (rightBase x)).isLeft = false := by
      rw [← partitionAt f (rightBase x)]
      exact rightFlag x
    cases hf : f (rightBase x) <;> simp_all)

theorem rightExtractSpec {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r))
    (x : Vertex (rightCode C (partition f))) :
    f (rightBase x) = Sum.inr (rightExtract f x) := by
  exact (Sum.inr_getRight _ _).symm

def extractLeftEmbedding {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r)) :
    codeGraph (leftCode C (partition f)) ↪g graph l where
  toFun := leftExtract f
  inj' := by
    intro x y h
    have he : leftBase x = leftBase y := f.injective (by
      rw [leftExtractSpec f x, leftExtractSpec f y, h])
    exact Subtype.ext (congrArg (fun z : Vertex C => z.val) he)
  map_rel_iff' := by
    intro x y
    change Adj l (leftExtract f x) (leftExtract f y) ↔
      (codeGraph (leftCode C (partition f))).Adj x y
    calc
      Adj l (leftExtract f x) (leftExtract f y) ↔
          Adj (.node o l r) (f (leftBase x)) (f (leftBase y)) := by
        rw [leftExtractSpec f x, leftExtractSpec f y]
        rfl
      _ ↔ (codeGraph C).Adj (leftBase x) (leftBase y) := f.map_rel_iff
      _ ↔ (codeGraph (leftCode C (partition f))).Adj x y := Iff.rfl

def extractRightEmbedding {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r)) :
    codeGraph (rightCode C (partition f)) ↪g graph r where
  toFun := rightExtract f
  inj' := by
    intro x y h
    have he : rightBase x = rightBase y := f.injective (by
      rw [rightExtractSpec f x, rightExtractSpec f y, h])
    exact Subtype.ext (congrArg (fun z : Vertex C => z.val) he)
  map_rel_iff' := by
    intro x y
    change Adj r (rightExtract f x) (rightExtract f y) ↔
      (codeGraph (rightCode C (partition f))).Adj x y
    calc
      Adj r (rightExtract f x) (rightExtract f y) ↔
          Adj (.node o l r) (f (rightBase x)) (f (rightBase y)) := by
        rw [rightExtractSpec f x, rightExtractSpec f y]
        rfl
      _ ↔ (codeGraph C).Adj (rightBase x) (rightBase y) := f.map_rel_iff
      _ ↔ (codeGraph (rightCode C (partition f))).Adj x y := Iff.rfl

theorem partitionCompatible {N} {C : Code N} {o l r}
    (f : codeGraph C ↪g graph (.node o l r)) : Compatible o C (partition f) := by
  intro x y hx hy hn
  let vx : Vertex C := ⟨x, hx⟩
  let vy : Vertex C := ⟨y, hy⟩
  have px := partitionAt f vx
  have py := partitionAt f vy
  change partition f x = (f vx).isLeft at px
  change partition f y = (f vy).isLeft at py
  have he : Adj (.node o l r) (f vx) (f vy) ↔
      (x ≠ y ∧ (C.2 x y = true ∨ C.2 y x = true)) := f.map_rel_iff
  cases hfx : f vx with
  | inl a =>
    cases hfy : f vy with
    | inl b =>
      exact False.elim (hn (by rw [px, py, hfx, hfy]; rfl))
    | inr b =>
      rw [hfx, hfy] at he
      exact he.symm
  | inr a =>
    cases hfy : f vy with
    | inl b =>
      rw [hfx, hfy] at he
      exact he.symm
    | inr b =>
      exact False.elim (hn (by rw [px, py, hfx, hfy]; rfl))

theorem splitEmbedding : Targets.SplitEmbedding := by
  intro N o l r C
  constructor
  · rintro ⟨f⟩
    exact ⟨partition f, ⟨extractLeftEmbedding f⟩, ⟨extractRightEmbedding f⟩,
      partitionCompatible f⟩
  · rintro ⟨P, ⟨f⟩, ⟨g⟩, hc⟩
    exact ⟨combineEmbedding o f g hc⟩

theorem runExact : Targets.RunExact := by
  intro N t
  induction t with
  | atom => exact leafExact N
  | node o l r ihl ihr =>
    intro C
    change C ∈ transition o (run N l) (run N r) ↔ Profile C (.node o l r)
    rw [splitEmbedding N o l r C]
    simp only [transition, Finset.mem_filter, Finset.mem_univ, true_and, ihl, ihr]

theorem acceptanceExact : Targets.AcceptanceExact := by
  intro N F t
  constructor
  · intro h C hC hp
    exact h C hC ((runExact N t C).mpr hp)
  · intro h C hC hm
    exact h C hC ((runExact N t C).mp hm)

theorem avoidanceDownward : Targets.AvoidanceDownward := by
  intro N F s t hst ht C hC hs
  obtain ⟨f⟩ := hs
  obtain ⟨g⟩ := RankedParse.Proof.homeomorphicInduced s t hst
  exact ht C hC ⟨(RankedParse.Proof.asGraphEmbedding g).comp f⟩

end LogicLineages.ModelsAlgebra.Forests.FiniteProfile.Proof
