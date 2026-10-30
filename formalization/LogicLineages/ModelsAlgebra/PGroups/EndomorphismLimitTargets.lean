module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupLimitStageInjective : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G), Function.Injective f →
    ∀ i : ℕ, Function.Injective (limitStage f i)

def groupLimitStageCompatibility : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G) (i j : ℕ) (hij : i ≤ j) (x : G),
    limitStage f j (iterationTransition f i j hij x) = limitStage f i x

def groupLimitRangesMonotone : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G),
    Monotone (fun i : ℕ => (limitStage f i).range)

def groupLimitRangeCover : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G) (x : EndomorphismLimit f),
    ∃ i : ℕ, x ∈ (limitStage f i).range

def groupEndomorphismLimitCountable : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] (f : G →+ G),
    Countable (EndomorphismLimit f)

end LogicLineages.ModelsAlgebra.PGroups.Targets
