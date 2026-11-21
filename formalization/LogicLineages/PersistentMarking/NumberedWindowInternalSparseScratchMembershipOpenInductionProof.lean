module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMinimumRowsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (invariant invariantCode invariantIndex)
open NumberedWindowInternalSparseScratchMembershipOpenMinimumRowsProof (minimumNil minimumCons)

private theorem constructorDerivation (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (invariant k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (invariant k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := selectedOccurs t (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (invariant k) 2).imp (atIndex (invariant k) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := minimumCons (body := body) (Γ := Δ) n h t (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- The induction is inside the original arithmetic proof calculus.
The candidate is arbitrary and fixed; the scratch list code is the
single quantity generalized by the actual list induction schema. -/
theorem occurs : ExactOpenScratchMinimumOccurs := by
  intro body α Γ code k
  have base : Nonempty (Derivation body Γ (atCode (invariant k) z)) := by
    rw [invariantCode]
    exact minimumNil k
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := constructorDerivation body α Γ k
  have original : Nonempty (Derivation body Γ (premises (invariant k))) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have current := actualOriginalListInductionAtCode body α Γ (invariant k) code original
  rw [invariantCode] at current
  exact current

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenInductionProof
