import LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionTargets
open NumberedWindowSyntax NumberedWindowRules
open NumberedWindowPreservationBoundProof (Compatible)

def HasBottomValue (values : NArgs) : Prop := ∃ ρ, NTerm.bottom ρ ∈ values.toList

/-- A supplied typed original raw edge remains a single typed raw edge,
except that the two images may be literally equal when the environment
substitutes a bottom. -/
def SubstitutionWindowStep : Prop :=
  ∀ S K C D τ q r values depth,
    DecisionSourceUniverse.Closed K → Compatible S K values depth C D →
    WindowStep S K C τ q r →
      WindowStep S K D τ (substitute values depth q) (substitute values depth r) ∨
      (substitute values depth q = substitute values depth r ∧ HasBottomValue values)

/-- Opening a literal bound slot with a typed free name retains a genuine
raw step. Freshness is unnecessary for this preservation direction. -/
def FreeSubstitutionWindowStep : Prop :=
  ∀ S K C σ τ q r name,
    DecisionSourceUniverse.Closed K → σ ∈ K → WindowStep S K (C.push σ) τ q r →
      WindowStep S K C τ (substitute (.cons (.free σ name) .nil) 0 q)
        (substitute (.cons (.free σ name) .nil) 0 r)

end LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionTargets
