module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision.Targets
open FirstOrder Language

def EncodedExact : Prop := ∀ (Q : Type) n (e : Q ≃ Fin n) (p : presburger.Formula Q),
  satisfiableEncoded e p = true ↔ ∃ v : Q → Nat, Formula.Realize p v

def OrderedExact : Prop := ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (p : presburger.Formula Q),
  satisfiable p = true ↔ ∃ v : Q → Nat, Formula.Realize p v
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision.Targets
