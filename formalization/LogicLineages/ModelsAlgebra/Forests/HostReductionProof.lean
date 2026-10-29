module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionTargets
public import Mathlib.Data.Fintype.Sum

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.HostReductionProof

variable {F G H : FiniteOrderForest}

def inclusion (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    JointImage f g ↪o H.Carrier where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by intro x y; rfl

def leftEmbedding (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    F.Carrier ↪o JointImage f g where
  toFun := jointImageLeftFun f g
  inj' := by
    intro x y h
    exact f.injective (congrArg Subtype.val h)
  map_rel_iff' := by intro x y; exact f.le_iff_le

def rightEmbedding (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    G.Carrier ↪o JointImage f g where
  toFun := jointImageRightFun f g
  inj' := by
    intro x y h
    exact g.injective (congrArg Subtype.val h)
  map_rel_iff' := by intro x y; exact g.le_iff_le

theorem forbiddenAvoidanceHereditary : Targets.ForbiddenAvoidanceHereditary := by
  intro U α β instα instβ e hAvoid B hB hEmb
  obtain ⟨b⟩ := hEmb
  exact hAvoid B hB ⟨b.trans e⟩

theorem inclusion_range (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    Set.range (inclusion f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem jointImageFactorization : Targets.JointImageFactorization := by
  intro F G H f g
  exact ⟨inclusion f g, leftEmbedding f g, rightEmbedding f g,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    inclusion_range f g⟩

theorem jointImageForest : Targets.JointImageForest := by
  intro F G H f g x y z hxz hyz
  exact H.forest hxz hyz

theorem jointImageAvoidance : Targets.JointImageAvoidance := by
  intro U F G H f g hAvoid
  exact forbiddenAvoidanceHereditary U (JointImage f g) H.Carrier (inclusion f g) hAvoid

theorem jointImageCardBound : Targets.JointImageCardBound := by
  intro F G H f g
  let cover : F.Carrier ⊕ G.Carrier → JointImage f g :=
    Sum.elim (jointImageLeftFun f g) (jointImageRightFun f g)
  have hs : Function.Surjective cover := by
    intro x
    rcases x.property with h | h
    · obtain ⟨a, ha⟩ := h
      refine ⟨Sum.inl a, ?_⟩
      apply Subtype.ext
      exact ha
    · obtain ⟨b, hb⟩ := h
      refine ⟨Sum.inr b, ?_⟩
      apply Subtype.ext
      exact hb
  simpa using Fintype.card_le_of_surjective cover hs

noncomputable def reducedForest (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier) :
    FiniteOrderForest where
  Carrier := JointImage f g
  carrierFintype := jointImageFintype f g
  carrierPartialOrder := inferInstance
  forest := jointImageForest F G H f g

theorem reducedCommonHost : Targets.ReducedCommonHost := by
  intro U F G H f g hAvoid
  refine ⟨reducedForest f g, jointImageAvoidance U F G H f g hAvoid,
    jointImageCardBound F G H f g, inclusion f g, leftEmbedding f g, rightEmbedding f g,
    inclusion_range f g, fun _ => rfl, fun _ => rfl⟩

theorem boundedCommonHost : Targets.BoundedCommonHost := by
  intro U F G
  constructor
  · rintro ⟨H, hAvoid, ⟨f⟩, ⟨g⟩⟩
    obtain ⟨K, hK, hcard, ι, left, right, hι, hleft, hright⟩ :=
      reducedCommonHost U F G H f g hAvoid
    exact ⟨K, hK, ⟨left⟩, ⟨right⟩, hcard⟩
  · rintro ⟨K, hK, left, right, hcard⟩
    exact ⟨K, hK, left, right⟩

end LogicLineages.ModelsAlgebra.Forests.HostReductionProof
