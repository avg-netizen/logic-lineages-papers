module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveBindingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionProof (strongInduction)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D)
open NumberedWindowInternalLiteralFuelMotiveSyntaxProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem measureIntro (p other : Program 3) (w : OTerm α)
    (h : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q r k : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) → D B Δ (Row p other q (w.relabel j) r k)) :
    D B Γ (Measure p other w) := by
  apply ID1Completion.InternalClosedProgramsBindingProof.introduction B α 3 Γ (Matrix p other w)
  let j : α → α ⊕ Fin 3 := Sum.inl
  exact h (α ⊕ Fin 3) j (Γ.map (fun f => f.relabel j))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (fun f hf => List.mem_map.mpr ⟨f,hf,rfl⟩)

theorem measureAt (p other : Program 3) (q w r k : OTerm α)
    (h : D B Γ (Measure p other w)) : D B Γ (Row p other q w r k) := by
  obtain ⟨d⟩ := ID1Completion.InternalClosedProgramsBindingProof.elimination B α 3 Γ
    (Matrix p other w) (fun i => emb (![q,r,k] i)) h
  rw [matrixWitness] at d
  exact ⟨d⟩

theorem smallerAt (p other : Program 3) (w v : OTerm α)
    (h : D B Γ (Smaller p other w)) (lt : D B Γ (ltF v w)) : D B Γ (Measure p other v) := by
  obtain ⟨d⟩ := h
  obtain ⟨less⟩ := lt
  have clause := Derivation.universalElimination (emb v) d
  change Derivation B Γ (instantiate ((ltF (.var (.inr 0)) (w.relabel Sum.inl)).imp
    (Predicate p other)) (emb v)) at clause
  rw [belowElimSyntax,predicateInstantiate] at clause
  exact ⟨Derivation.implicationElimination clause less⟩

/-- Generalization before induction is essential: every smaller witness
is usable at independent raw endpoints and independently sized surplus
fuel, not just the endpoints traversed by the parent. -/
theorem strongMeasure (p other : Program 3) (w : OTerm α)
    (step : ∀ (β : Type) (Δ : List (Formula β)) (v : OTerm β),
      D B Δ (Smaller p other v) → D B Δ (Measure p other v)) :
    D B Γ (Measure p other w) := by
  let θ : Formula (α ⊕ Fin 1) := Predicate p other
  have inductionStep : D B (below (lift θ) (.var (.inr 0)) :: Γ.map weaken) θ := by
    change D B (below (lift (Predicate p other)) (.var (.inr 0)) :: Γ.map weaken)
      (Measure p other (.var (.inr 0)))
    rw [predicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨all⟩ := strongInduction θ inductionStep
  have d := Derivation.universalElimination (emb w) all
  change Derivation B Γ (instantiate (Predicate p other) (emb w)) at d
  rw [predicateInstantiate] at d
  exact ⟨d⟩

#print axioms measureIntro
#print axioms smallerAt
#print axioms strongMeasure
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveBindingProof
