module
public import LogicLineages.ModelsAlgebra.Forests.ForestParikhTransitionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates ForestParseRepresentationCounts CotreeMachineParikh

def StateSetTransport : Prop := ∀ (M : Machine) k (e : M.State ≃ Fin k) C,
  stateSet (numberMachine M e).toMachine C = e.finsetCongr (stateSet M C)

/-- Exact count-vector transport, including the multiplicity of repeated equal children. -/
def ChildCountTransport : Prop := ∀ (M : Machine) k (e : M.State ≃ Fin k)
    n (c : Fin n → Cotree) B,
  childCounts (numberMachine M e).toMachine c B = childCounts M c (e.finsetCongr.symm B)

/-- Source equation (4) with no extra order hypothesis: numbering is explicit finite input. -/
def NumberedParikhExact : Prop := ∀ (M : Machine) k (e : M.State ≃ Fin k)
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔ (compileNumbered M e o q).Realize (childCounts M c)

/-- Semantic completeness for every abstract finite machine. Choosing an encoding
inside this existential proof is not asserted to be an executable input conversion;
the actual compiler above consumes the explicitly supplied finite numbering. -/
def SemanticCompleteness : Prop := ∀ M : Machine, ∃ k, ∃ e : M.State ≃ Fin k,
  ∀ o n (c : Fin (n + 2) → Cotree) q,
    q ∈ stateSet M (.node o n c) ↔ (compileNumbered M e o q).Realize (childCounts M c)

end LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.Targets
