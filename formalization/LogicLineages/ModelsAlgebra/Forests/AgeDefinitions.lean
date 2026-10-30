module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionDefinitions
public import Mathlib.Data.Countable.Defs

/-! Literal classes and finite/countable forest ages, paper03 prop:age.
Heredity is under ordinary induced-order embeddings, so it includes isomorphism
invariance. Empty finite forests are allowed. No realization theorem is assumed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeConstruction

structure CountableOrderForest where
  Carrier : Type
  carrierPartialOrder : PartialOrder Carrier
  carrierCountable : Countable Carrier
  forest : @IsOrderForest Carrier carrierPartialOrder

attribute [instance] CountableOrderForest.carrierPartialOrder CountableOrderForest.carrierCountable

def ClassNonempty (K : FiniteOrderForest → Prop) : Prop := ∃ F, K F

def ClassHereditary (K : FiniteOrderForest → Prop) : Prop :=
  ∀ F G : FiniteOrderForest, K F → Nonempty (G.Carrier ↪o F.Carrier) → K G

def ClassHasJEP (K : FiniteOrderForest → Prop) : Prop :=
  ∀ F G : FiniteOrderForest, K F → K G →
    ∃ H : FiniteOrderForest, K H ∧
      Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier)

def HasForestAge (K : FiniteOrderForest → Prop) (A : CountableOrderForest) : Prop :=
  ∀ F : FiniteOrderForest, K F ↔ Nonempty (F.Carrier ↪o A.Carrier)

def ClassUnbounded (K : FiniteOrderForest → Prop) : Prop :=
  ∀ n : Nat, ∃ F : FiniteOrderForest, K F ∧ n < Fintype.card F.Carrier

end LogicLineages.ModelsAlgebra.Forests.AgeConstruction
