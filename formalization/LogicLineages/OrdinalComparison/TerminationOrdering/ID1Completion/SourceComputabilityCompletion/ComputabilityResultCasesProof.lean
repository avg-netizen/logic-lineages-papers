module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityResultCasesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalComputabilityApplicationSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm)

/-- Eliminate the ORIGINAL existential returned by C at arrow type. Both
the actual application certificate and codomain C are retained; no output
value is guessed or obtained from an external semantic witness. -/
theorem resultCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (sigma tau : Ty) (context f a : OTerm α) (psi : Formula α)
    (hr : Nonempty (Derivation body Gamma (resultExists comp sigma tau context f a)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (accepted comp sigma tau (context.relabel j) (f.relabel j) (a.relabel j) out)) →
      Nonempty (Derivation body Delta (computable comp tau (context.relabel j) out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hr⟩ := hr
  let R := resultBody comp sigma tau context f a
  let Delta := R :: Gamma.map weaken
  have hh : Derivation body Delta R := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft hh⟩ ⟨Derivation.conjunctionRight hh⟩
  exact ⟨Derivation.existentialElimination hr d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityResultCasesProof
