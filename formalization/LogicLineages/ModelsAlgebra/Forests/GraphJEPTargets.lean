module

public import LogicLineages.ModelsAlgebra.Forests.GraphJEPDefinitions

/-! Exact semantic reduction in paper 03 `thm:decision`. These targets do not
assert effective decidability and do not assume Carter's missing theorem.
Empty finite carriers and empty permitted classes are included. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def GraphAvoidanceIsoInvariant : Prop :=
  ∀ (U : List FiniteOrderForest) (G H : FiniteSimpleGraph) (e : G.graph ≃g H.graph),
    GraphAvoidsForbidden U G ↔ GraphAvoidsForbidden U H

def ComparabilityAvoidance : Prop :=
  ∀ (U : List FiniteOrderForest) (F : FiniteOrderForest),
    GraphAvoidsForbidden U (finiteComparabilityGraph F) ↔ AvoidsForbidden U F.Carrier

def ForbiddenGraphRepresented : Prop :=
  ∀ (U : List FiniteOrderForest) (G : FiniteSimpleGraph), GraphAvoidsForbidden U G →
    ∃ F : FiniteOrderForest, AvoidsForbidden U F.Carrier ∧
      Nonempty (G.graph ≃g comparabilityGraph F)

def ForbiddenFamilyJEPEquivalence : Prop :=
  ∀ U : List FiniteOrderForest, CertificateSearch.HasJEP U ↔ GraphHasJEP U

end LogicLineages.ModelsAlgebra.Forests.Targets
