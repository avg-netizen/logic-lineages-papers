module
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.Targets
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular ForestParseRepresentation

def ReachableHeightExact : Prop :=
  ∀ (M : Machine) [DecidableEq M.State] n s,
    s ∈ reachable M n ↔ ∃ t, termHeight t ≤ n ∧ machineRun M t = s

def ReachableSaturation : Prop :=
  ∀ (M : Machine) [DecidableEq M.State],
    reachable M (Fintype.card M.State + 1) = reachable M (Fintype.card M.State)

def MachineEmptyCorrect : Prop :=
  ∀ (M : Machine) [DecidableEq M.State],
    languageEmpty M = true ↔ ¬ ∃ t, M.accept (machineRun M t) = true

/-- Exact executable L-empty exceptional branch of the source decision proof,
including empty forbidden graphs. No JEP or ideal-decomposition oracle. -/
def SourceEmptyCorrect : Prop :=
  ∀ F, sourceLanguageEmpty F = true ↔
    ¬ ∃ t, GeneralForbiddenLanguage (F.map rawFinite) t

end LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.Targets
