module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomatonDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree

def NodeStepExact : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] o n (c : Fin (n + 2) → Cotree) s,
    (nodeFormula M o s).Realize (fun a => (List.ofFn (fun i => expected M (c i))).count a) ↔
      s = expected M (.node o n c) ∧ ∀ i, root (c i) ≠ some o

def RunsExact : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] C s,
    Runs M C s ↔ Reduced C ∧ s = expected M C

def RunsDeterministic : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] C s t, Runs M C s → Runs M C t → s = t

/-- Exact reduced-cotree graph-image acceptance, not just a chosen binary representative. -/
def AcceptanceExact : Prop :=
  ∀ (M : Machine) [LinearOrder M.State] C,
    (∃ s, Runs M C s ∧ accept M s = true) ↔
      Reduced C ∧ ∃ t, Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ∧
        M.accept (machineRun M t) = true

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.Targets
