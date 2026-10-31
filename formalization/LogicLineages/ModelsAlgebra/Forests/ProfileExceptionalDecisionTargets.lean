module
public import LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.Targets
open RankedGraphImage ProfileAutomatonEncoding ProfileSourceRegular ForestParseRepresentation

def EmptyInputCorrect : Prop :=
  ∀ F, hasEmptyForbidden F = true ↔ ∃ A ∈ F, A.1 = 0

def EmptyForbiddenCase : Prop :=
  ∀ (B : List FiniteGraph), (∃ H ∈ B, IsEmpty H.Vertex) →
    (∀ G, ¬ GeneralForbiddenClass B G) ∧ GraphJEP (GeneralForbiddenClass B)

def EmptyLanguageCase : Prop :=
  ∀ (B : List FiniteGraph), (∀ H ∈ B, Nonempty H.Vertex) →
    (¬ ∃ t, GeneralForbiddenLanguage B t) →
    (∀ G, GeneralForbiddenClass B G → IsEmpty G.Vertex) ∧
      GraphJEP (GeneralForbiddenClass B)

/-- Soundness of the actual explicit partial decision function. It deliberately
returns no answer on the unresolved nonempty-language general case. -/
def ExceptionSound : Prop :=
  ∀ F, exceptionalDecision F = some true →
    GraphJEP (GeneralForbiddenClass (F.map rawFinite))

end LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.Targets
