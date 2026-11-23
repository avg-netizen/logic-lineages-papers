module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationSubstitutionProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRules

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open Spine (ArrowPrefix)
open NumberedWindowApplicationTargets (ArgsWindow)
open NumberedWindowPreservationBoundProof (Compatible)

def SubstitutionPreservesMarkDecrease : Prop :=
  ∀ values depth q r, MarkDecrease q r →
    MarkDecrease (substitute values depth q) (substitute values depth r)

def SubstitutionPreservesPrimitiveReplacement : Prop :=
  ∀ values depth source target, PrimitiveReplacement source target →
    PrimitiveReplacement (substituteArgs values depth source) (substituteArgs values depth target)

/-- The actual fully typed argument tuple and the left-associated original
auxiliary applications commute with the same literal substitution. -/
def TypedSubstitutionApplications : Prop :=
  ∀ S K C D ds τ q args values depth, DecisionSourceUniverse.Closed K →
    Compatible S K values depth C D → InWindow S K C (ArrowPrefix ds τ) q →
    ArgsWindow S K C ds args →
    applications (substitute values depth q) (substituteArgs values depth args) =
      (applications q args).map (substitute values depth)

/-- Restore the same selected occurrence, its exact arrow annotation,
and its successful full literal auxiliary call after substitution. -/
def TypedSubstitutionSelect : Prop :=
  ∀ S K C D f τ k bs es i selected ds result values depth,
    DecisionSourceUniverse.Closed K → Compatible S K values depth C D →
    InWindow S K C τ (.numbered f τ (k + 1) bs es) →
    (bs.get i = some selected ∨ es.get i = some selected) →
    selected.type = ArrowPrefix ds τ → applications selected (ownerCopies f k bs es ds) = some result →
    ((substituteArgs values depth bs).get i = some (substitute values depth selected) ∨
      (substituteArgs values depth es).get i = some (substitute values depth selected)) ∧
    (substitute values depth selected).type = ArrowPrefix ds τ ∧
    applications (substitute values depth selected)
      (ownerCopies f k (substituteArgs values depth bs) (substituteArgs values depth es) ds) =
        some (substitute values depth result)

end LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionTargets
