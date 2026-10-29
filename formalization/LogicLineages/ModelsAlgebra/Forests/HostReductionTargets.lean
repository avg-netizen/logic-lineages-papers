module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionDefinitions

/-! Independently frozen semantic targets for paper 03's common-host bound.
These do not assert a finite encoding, a computable exhaustive certificate,
a bound on the first bad pair, Carter's algorithm, or JEP decidability. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def ForbiddenAvoidanceHereditary : Prop :=
  ∀ (U : List FiniteOrderForest) (α β : Type) [PartialOrder α] [PartialOrder β]
      (e : α ↪o β), AvoidsForbidden U β → AvoidsForbidden U α

def JointImageFactorization : Prop :=
  ∀ (F G H : FiniteOrderForest) (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier),
    ∃ (ι : JointImage f g ↪o H.Carrier)
      (left : F.Carrier ↪o JointImage f g) (right : G.Carrier ↪o JointImage f g),
      (∀ x, ι x = x.val) ∧
      (∀ x, left x = jointImageLeftFun f g x) ∧
      (∀ x, right x = jointImageRightFun f g x) ∧
      (∀ x, ι (left x) = f x) ∧ (∀ x, ι (right x) = g x) ∧
      Set.range ι = Set.range f ∪ Set.range g

def JointImageForest : Prop :=
  ∀ (F G H : FiniteOrderForest) (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier),
    IsOrderForest (JointImage f g)

def JointImageAvoidance : Prop :=
  ∀ (U : List FiniteOrderForest) (F G H : FiniteOrderForest)
      (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier),
    AvoidsForbidden U H.Carrier → AvoidsForbidden U (JointImage f g)

def JointImageCardBound : Prop :=
  ∀ (F G H : FiniteOrderForest) (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier),
    Fintype.card (JointImage f g) ≤ Fintype.card F.Carrier + Fintype.card G.Carrier

/-- Actual reduced host with its inclusion into the original host, exact
union image, original-embedding factorizations and source cardinal bound. -/
def ReducedCommonHost : Prop :=
  ∀ (U : List FiniteOrderForest) (F G H : FiniteOrderForest)
      (f : F.Carrier ↪o H.Carrier) (g : G.Carrier ↪o H.Carrier),
    AvoidsForbidden U H.Carrier →
      ∃ K : FiniteOrderForest,
        AvoidsForbidden U K.Carrier ∧
        Fintype.card K.Carrier ≤ Fintype.card F.Carrier + Fintype.card G.Carrier ∧
        ∃ (ι : K.Carrier ↪o H.Carrier) (left : F.Carrier ↪o K.Carrier)
          (right : G.Carrier ↪o K.Carrier),
          Set.range ι = Set.range f ∪ Set.range g ∧
          (∀ x, ι (left x) = f x) ∧ (∀ x, ι (right x) = g x)

/-- A common permitted finite forest exists iff one exists with at most the
sum of the two given sizes. This is a host bound for a fixed pair only. -/
def BoundedCommonHost : Prop :=
  ∀ (U : List FiniteOrderForest) (F G : FiniteOrderForest),
    (∃ H : FiniteOrderForest, AvoidsForbidden U H.Carrier ∧
      Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier)) ↔
    (∃ K : FiniteOrderForest, AvoidsForbidden U K.Carrier ∧
      Nonempty (F.Carrier ↪o K.Carrier) ∧ Nonempty (G.Carrier ↪o K.Carrier) ∧
      Fintype.card K.Carrier ≤ Fintype.card F.Carrier + Fintype.card G.Carrier)

end LogicLineages.ModelsAlgebra.Forests.Targets
