module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.Targets
open ProfileAutomatonEncoding CotreePresburgerBoolean

def ProductRunsExact : Prop :=
  ∀ (Q R : Type) [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R) C s,
    Runs (product A B) C s ↔ Runs A C (ofLex s).1 ∧ Runs B C (ofLex s).2

def ProductLanguageExact : Prop :=
  ∀ (Q R : Type) [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R) C,
    Language (product A B) C ↔ Language A C ∧ Language B C

def ProductComplete : Prop :=
  ∀ (Q R : Type) [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R),
    CompleteDeterministic A → CompleteDeterministic B → CompleteDeterministic (product A B)

def DifferenceLanguageExact : Prop :=
  ∀ (Q R : Type) [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R), CompleteDeterministic B → ∀ C,
    Language (difference A B) C ↔ Language A C ∧ ¬ Language B C

/-- Exact semantic reduction using the explicitly constructed difference;
no emptiness decision oracle or inclusion algorithm is assumed. -/
def InclusionToEmpty : Prop :=
  ∀ (Q R : Type) [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R), CompleteDeterministic B →
    ((∀ C, Language A C → Language B C) ↔ Empty (difference A B))

/-- The complete/deterministic premise is discharged for the actual source compiler. -/
def SourceInclusionToEmpty : Prop :=
  ∀ (M N : Machine) [LinearOrder M.State] [LinearOrder N.State],
    ((∀ C, Language (source M) C → Language (source N) C) ↔
      Empty (difference (source M) (source N)))

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.Targets
