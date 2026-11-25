module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralAtomicRawGuardProof
  (guardedRaw atRawSource freeTest bottomTest exactRawBottom)

attribute [local irreducible] programGraph

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem atSourceGraph (p : Program 1) (b : OTerm α) (args : Fin 5 → OTerm α)
    (held : D B Γ (unary p b (args 2))) :
    D B Γ (programGraph (atRawSource p) b args) := by
  apply compositionValue p (fun _ : Fin 1 => .projection 2) b args ![args 2] held
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 2 args

private theorem rejectedConstant (args : Fin 5 → OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (constantZero 5) (suc z) args)) :
    D B Γ goal := by
  obtain ⟨bad⟩ := valueUnique (constantZero 5) (suc z) z args held (constantZeroValue args)
  exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

/-- The guard may be removed from an actual positive raw graph inside
the same derivation body; no agreement of compiled outputs is used. -/
theorem exact_OpenLiteralAtomicRawUnderlying (raw : Program 5) (args : Fin 5 → OTerm α)
    (held : D B Γ (programGraph (guardedRaw raw) (suc z) args)) :
    D B Γ (programGraph raw (suc z) args) := by
  let F := atRawSource freeTest
  let T := atRawSource bottomTest
  let bad := constantZero 5
  let side := branch T raw bad
  let main := conjunction raw exactRawBottom
  apply optionGraphCases F args (programGraph raw (suc z) args)
  · intro β j Δ keep notFree
    rw [programRename,sucRelabel,zRelabel]
    let xs := fun k => (args k).relabel j
    have same := renameInto held j Δ keep
    simp only [programRename,sucRelabel,zRelabel] at same
    have inner := zeroBranchElim F side main (suc z) xs notFree same
    apply optionGraphCases T xs (programGraph raw (suc z) xs)
    · intro γ l Ω stay notBottom
      rw [programRename,sucRelabel,zRelabel]
      have selected := renameInto inner l Ω stay
      simp only [programRename,sucRelabel,zRelabel] at selected
      exact zeroBranchElim T raw bad (suc z) _ notBottom selected
    · intro γ l Ω pred stay bottom
      have selected := renameInto inner l Ω stay
      simp only [programRename,sucRelabel,zRelabel] at selected
      exact rejectedConstant _ _ (successorBranchElim T raw bad (suc z) pred _ bottom selected)
  · intro β j Δ pred keep free
    rw [programRename,sucRelabel,zRelabel]
    let xs := fun k => (args k).relabel j
    have same := renameInto held j Δ keep
    simp only [programRename,sucRelabel,zRelabel] at same
    have selected := successorBranchElim F side main (suc z) pred xs free same
    obtain ⟨row⟩ := conjunctionRecover raw exactRawBottom xs selected
    exact ⟨Derivation.conjunctionLeft row⟩

/-- On the physically tested free arm, the accepted original callback
and exact bottom-target comparison hold on the very same tape. -/
theorem exact_OpenLiteralAtomicRawFreeGuard (raw : Program 5) (args : Fin 5 → OTerm α)
    (free : D B Γ (unary freeTest (suc z) (args 2)))
    (held : D B Γ (programGraph (guardedRaw raw) (suc z) args)) :
    D B Γ (programGraph raw (suc z) args ⊓ programGraph exactRawBottom (suc z) args) :=
  conjunctionRecover raw exactRawBottom args
    (successorBranchElim (atRawSource freeTest)
      (branch (atRawSource bottomTest) raw (constantZero 5))
      (conjunction raw exactRawBottom) (suc z) z args (atSourceGraph freeTest (suc z) args free) held)

/-- On the physically tested bottom arm, acceptance is impossible. -/
theorem exact_OpenLiteralAtomicRawBottomGuard (raw : Program 5) (args : Fin 5 → OTerm α)
    (notFree : D B Γ (unary freeTest z (args 2)))
    (bottom : D B Γ (unary bottomTest (suc z) (args 2)))
    (held : D B Γ (programGraph (guardedRaw raw) (suc z) args)) :
    D B Γ ⊥ := by
  have inner := zeroBranchElim (atRawSource freeTest)
    (branch (atRawSource bottomTest) raw (constantZero 5)) (conjunction raw exactRawBottom)
    (suc z) args (atSourceGraph freeTest z args notFree) held
  have called := successorBranchElim (atRawSource bottomTest) raw (constantZero 5)
    (suc z) z args (atSourceGraph bottomTest (suc z) args bottom) inner
  exact rejectedConstant args ⊥ called

#print axioms exact_OpenLiteralAtomicRawUnderlying
#print axioms exact_OpenLiteralAtomicRawFreeGuard
#print axioms exact_OpenLiteralAtomicRawBottomGuard
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
