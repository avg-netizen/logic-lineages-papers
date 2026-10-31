module
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteProfile.Targets
open RankedParse

def LeafExact : Prop := ∀ N (C : Code N), C ∈ leafState N ↔ Profile C .atom

def SplitEmbedding : Prop :=
  ∀ N (o : Operation) (l r : Term) (C : Code N),
    Profile C (.node o l r) ↔ ∃ P : Fin N → Bool,
      Profile (leftCode C P) l ∧ Profile (rightCode C P) r ∧ Compatible o C P

def RunExact : Prop := ∀ N (t : Term) (C : Code N), C ∈ run N t ↔ Profile C t

def AcceptanceExact : Prop :=
  ∀ N (F : List (Code N)) (t : Term), Accepts F (run N t) ↔ Avoids F t

def AvoidanceDownward : Prop :=
  ∀ N (F : List (Code N)) (s t : Term), Homeomorphic s t → Avoids F t → Avoids F s

end LogicLineages.ModelsAlgebra.Forests.FiniteProfile.Targets
