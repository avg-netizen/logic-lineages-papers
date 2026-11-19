import LogicLineages.PersistentMarking.NumberedWindowPathLocality
import LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets
import LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFullLocalityTargets
open LiteralDerivationTree LiteralDerivationLocalityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowClosing
open NumberedWindowPreservationTargets NumberedWindowPathLocality
open NumberedWindowOrdinaryTranslation NumberedWindowTupleTargets NumberedWindowSimulationData

/-- Same original defined complete tuple, actual inputs and exact finite
budget as WholeTupleSimulation. Assert admission of all literal visits
of its actual raw witness, not merely admissibility of its endpoints. -/
def ConstructedTupleLocality : Prop := ∀ (S : Spine.Signature) (K : List Ty) (Γ : List Ty)
    (q r : Spine.Expr) (args : Spine.Args) (σ τ : Ty) (n : Nat) (Q : NTerm) (As : NArgs),
  let C := Spine.BoundContext.prefix Γ Spine.EmptyContext
  DecisionSourceUniverse.Closed K →
  Spine.Typed C q σ → Spine.Valid S q → Spine.CallTyped C σ args τ → Spine.ValidArgs S args →
  SymbolicAdmissible K q → SymbolicArgsAdmissible K args →
  Spine.apply q args = some r →
  Realizes (NumberedWindowTupleTargets.budget n args) q Q →
  RealizesArgs (NumberedWindowTupleTargets.budget n args) args As →
  ∃ start out, applications Q As = some start ∧
    ∃ path : WindowPath S K C τ start out,
      AllVisitsAdmitted path ∧ Realizes n r out

/-- Actual complete weak simulation and its literal vertices in the same K.
No guard hypotheses at the generated intermediate or numerical vertices. -/
def ConstructedWeakLocality : Prop := ∀ S K q t (tree : Tree S (.weak q t)),
  DecisionSourceUniverse.Closed K → SymbolicAdmissible K q → SymbolicAdmissible K t →
  ∀ n Q, NumberedWindowSimulationData.budget tree ≤ n → Realizes n q Q →
    ∃ T, tr t = some T ∧
      ∃ path : TypedTrace S K Spine.EmptyContext q.type Q T,
        ∀ u ∈ vertices path, InWindow S K Spine.EmptyContext q.type u

/-- The actual complete strict construction additionally retains its
genuine positive raw length; equivalence steps do not count. -/
def ConstructedStrictLocality : Prop := ∀ S K q t (tree : Tree S (.strict q t)),
  DecisionSourceUniverse.Closed K → SymbolicAdmissible K q → SymbolicAdmissible K t →
  ∀ n Q, NumberedWindowSimulationData.budget tree ≤ n → Realizes n q Q →
    ∃ T, tr t = some T ∧
      ∃ path : TypedTrace S K Spine.EmptyContext q.type Q T,
        (∀ u ∈ vertices path, InWindow S K Spine.EmptyContext q.type u) ∧ 0 < rawLength path

/-- Numbered locality: every actual symbolic derivation vertex and every
actual numeric intermediate, including the manuscript's concrete paths. -/
def FullWindowLocality : Prop :=
  SymbolicLocality ∧ AllTypedTraceIntermediates ∧
    ConstructedTupleLocality ∧ ConstructedWeakLocality ∧ ConstructedStrictLocality

end LogicLineages.PersistentMarking.NumberedWindowFullLocalityTargets
