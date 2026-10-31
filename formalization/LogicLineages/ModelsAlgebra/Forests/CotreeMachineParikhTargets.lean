module
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates ForestParseRepresentationCounts

/-- Exact source equation (4), with all child occurrences and all binary representations. -/
def StateTransitionExact : Prop := ∀ (M : Machine) [LinearOrder M.State]
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔
    (transitionFormula M o q).Realize (childCounts M c)

/-- The same actual formula constructor for literal numerical finite-table inputs. -/
def TableTransitionExact : Prop := ∀ (T : TableMachine)
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet T.toMachine (.node o n c) ↔
    (tableFormula T o q).Realize (childCounts T.toMachine c)

def EncodingRunExact : Prop := ∀ (M : Machine) n (e : M.State ≃ Fin n) t,
  machineRun (numberMachine M e).toMachine t = e (machineRun M t)

/-- Semantic coverage of an arbitrary finite-state machine with an explicitly
supplied numbering; the effective compiler acts on the resulting literal table. -/
def NumberedTransitionExact : Prop := ∀ (M : Machine) k (e : M.State ≃ Fin k)
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔
    (tableFormula (numberMachine M e) o (e q)).Realize
      (childCounts (numberMachine M e).toMachine c)

end LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.Targets
