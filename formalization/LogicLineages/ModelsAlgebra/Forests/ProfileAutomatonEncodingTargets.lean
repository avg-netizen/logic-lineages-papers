module
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.Targets
open RankedParse FiniteProfile RankedGraphImage

def FamilyBoundCorrect : Prop := ∀ F A, A ∈ F → A.1 ≤ familyBound F

def EncodingIso : Prop :=
  ∀ N A, A.1 ≤ N → Nonempty (rawGraph A ≃g codeGraph (encode N A))

/-- Completeness of the conventional finite matrix representation, on actual
finite simple graphs. This semantic existence is not called by `machine`. -/
def FiniteGraphRepresentability : Prop :=
  ∀ G : FiniteGraph, ∃ A : RawGraph, Nonempty (G.edges ≃g rawGraph A)

/-- Exact correctness of the explicitly constructed finite-state ranked machine
on an arbitrary finite list of raw finite graph inputs, including empty graphs. -/
def MachineCorrect : Prop :=
  ∀ F t, (machine F).accept (machineRun (machine F) t) = true ↔ RawAvoids F t

def RawAvoidanceDownward : Prop :=
  ∀ F s t, Homeomorphic s t → RawAvoids F t → RawAvoids F s

/-- The exact arbitrary finite graph-family language, not merely a supplied
bounded-code surrogate, is recognized by one of the constructed machines. -/
def ArbitraryFiniteFamilyRegular : Prop :=
  ∀ Gs : List FiniteGraph, ∃ F : List RawGraph, ∀ t,
    (machine F).accept (machineRun (machine F) t) = true ↔
      ∀ G ∈ Gs, ¬ Nonempty (G.edges ↪g graph t)

end LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding.Targets
