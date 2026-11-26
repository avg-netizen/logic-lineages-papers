module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRawListRecursion (recGraph)
open NumberedWindowInternalOriginRowsFilterTargets (Report rowStep rowCell zeroBase)

abbrev filterGraph {α : Type} (side : Bool) (out input pool : OrdinaryArithmetic.Term α) :=
  recGraph zeroBase (rowStep side) out input ![pool]

def ExactOpenOriginFilterConsCases : Prop :=
  ∀ (side : Bool) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code head tail pool out : OrdinaryArithmetic.Term α) (goal : Formula α),
    Report B Γ (rowCell code head tail) →
    Report B Γ (filterGraph side out code pool) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OrdinaryArithmetic.Term β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Report B Δ (filterGraph side old (tail.relabel j) (pool.relabel j)) →
      Report B Δ (programGraph (rowStep side) (out.relabel j) ![head.relabel j,old,pool.relabel j]) →
      Report B Δ (goal.relabel j)) →
    Report B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesTargets
