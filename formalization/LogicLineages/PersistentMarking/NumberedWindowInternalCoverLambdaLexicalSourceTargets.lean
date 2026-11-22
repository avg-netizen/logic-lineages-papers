module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)
open NumberedWindowLexicalAlgorithm (Requirement binder holds)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)

/-- Exact original lexical push law on successful raw list decodes;
not a port extension or a protected observation relation. -/
def ExactCoverRawLexicalBinder : Prop :=
  ∀ (g : List Nat) (domain : Nat) (r : Requirement),
    holds (fun i => g[i]?) (binder domain r) = holds (fun i => (domain :: g)[i]?) r

/-- A positive original packed literal lambda pays the actual immediate
lexical body at the same original context with its stored type pushed. -/
def ExactCoverLambdaPackedLexicalProvenance : Prop :=
  ∀ (s : Settings) (ctx raw domain child : Nat),
    unpackNode raw = some (2,[domain,child]) →
    intrinsicWindow s ctx raw ≠ 0 →
    ∃ g : List Nat, unpack ctx = some g ∧ domain ∈ s.window.1 ∧
      intrinsicWindow s (pack (domain :: g)) child = intrinsicType child + 1 ∧
      intrinsicWindow s ctx raw = arrow domain (intrinsicType child) + 1

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets
