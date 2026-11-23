module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralParsedJ)
open NumberedWindowInternalOddProgressiveInductionProof
  (exact_OriginalOddLowerInstance exact_ActualOriginalOddProgressiveInduction)
open NumberedWindowInternalLiteralPackedJLexBlockTargets

theorem specializeClosedBlock {α β : Type} {k : Nat} (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k))
    (σ : α ⊕ Fin 1 → Term β) :
    (allBlock matrix).subst σ = allBlock (specialize matrix σ) :=
  allBlockSubst matrix σ

/-- The genuine original J induction, starting from the actual typed
parsed tape and actual object-level I instances of all its members.
Its result still quantifies every later constructor parameter. -/
theorem exact_OpenLiteralPackedJBlock : ExactOpenLiteralPackedJBlock := by
  intro i r c α k Γ matrix raw scratch parsed typed members progress
  obtain ⟨j⟩ := exact_LiteralParsedJ i r c α Γ raw scratch parsed typed members
  obtain ⟨ind⟩ := exact_ActualOriginalOddProgressiveInduction
    (literalData i r) c α Γ (allBlock matrix) raw progress
  have finish := Derivation.implicationElimination ind j
  unfold instantiate at finish
  rw [specializeClosedBlock] at finish
  exact ⟨finish⟩

/-- Actual certified odd successor lookup retains the whole later block.
In particular, a base-list descent can reset the later label or extras. -/
theorem exact_OpenLiteralPackedJLowerBlock : ExactOpenLiteralPackedJLowerBlock := by
  intro i r c α k Γ matrix large small witness lower cert
  obtain ⟨h⟩ := exact_OriginalOddLowerInstance (literalData i r) c Γ large small
    (allBlock matrix) lower (edgeIntroduction cert)
  rw [specializeClosedBlock] at h
  exact ⟨h⟩

theorem exact_OpenLiteralPackedJLaterInstance {α β : Type} {k : Nat}
    (i : Program 1) (r : Program 3) (c : Nat) (Γ : List (Formula β))
    (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k)) (σ : α ⊕ Fin 1 → Term β)
    (later : Fin k → OTerm β)
    (all : Pr (literalData i r) c Γ (allBlock (specialize matrix σ))) :
    Pr (literalData i r) c Γ (useLater matrix σ later) :=
  actualFiniteUniversalElimination _ β k Γ (specialize matrix σ) (fun j => emb (later j)) all

#print axioms exact_OpenLiteralPackedJBlock
#print axioms exact_OpenLiteralPackedJLowerBlock
#print axioms exact_OpenLiteralPackedJLaterInstance

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockProof
