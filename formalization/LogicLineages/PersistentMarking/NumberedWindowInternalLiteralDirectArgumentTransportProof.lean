module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectArgumentTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalNeutralFactsTargets (direct directData)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenDirectSourceTransport (data : Data) (h : Program 3) (c : Nat) (x x' y : OTerm α)
    (same : Nonempty (Derivation B Γ (eqn x x')))
    (source : Nonempty (Derivation B Γ (direct data h c x y))) :
    Nonempty (Derivation B Γ (direct data h c x' y)) := by
  let row := edge (directData data h) false c
    (.var (.inr (0 : Fin 1))) (y.relabel (Sum.inl : α → α ⊕ Fin 1))
  have inp (v : OTerm α) : instantiate row (emb v) = direct data h c v y := by
    simp only [row,direct,instantiate,bindEmbedding,edgeSubst,liftBind,varBind]
  obtain ⟨s⟩ := source
  obtain ⟨e⟩ := same
  exact ⟨(inp x') ▸ Derivation.equalityElimination row (emb x) (emb x') e ((inp x).symm ▸ s)⟩

#print axioms exact_OpenDirectSourceTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectArgumentTransportProof
