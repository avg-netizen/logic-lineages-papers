module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBooleanDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree

def SourceRunsExact : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] C q, Runs (source M) C q ↔ CotreePresburgerAutomaton.Runs M C q

def SourceLanguageExact : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] C,
    Language (source M) C ↔ Reduced C ∧ ∃ t,
      Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ∧
      M.accept (machineRun M t) = true

def SourceComplete : Prop :=
  ∀ (M : Machine) [LinearOrder M.State], CompleteDeterministic (source M)

def ComplementRunsExact : Prop :=
  ∀ (Q : Type) [DecidableEq Q] (A : Automaton Q) C q,
    Runs (complement A) C q ↔ Runs A C q

/-- The determinism/totality property is proved for the actual source compiler,
not supplied as a missing arithmetic decision algorithm. -/
def ComplementLanguageExact : Prop :=
  ∀ (Q : Type) [DecidableEq Q] (A : Automaton Q), CompleteDeterministic A →
    ∀ C, Language (complement A) C ↔ Reduced C ∧ ¬ Language A C

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.Targets
