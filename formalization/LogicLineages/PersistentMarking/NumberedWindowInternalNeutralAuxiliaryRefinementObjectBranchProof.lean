module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementASTProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementObjectBranchProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalAtomicRefinement (atSource atTarget bottomTarget)
open NumberedWindowInternalAuxBottomRefinement (refineAuxBottom)
open NumberedWindowInternalNeutralAuxiliaryRefinement
open NumberedWindowInternalNeutralAuxiliaryRefinementASTProof (exact_NeutralPositiveAST exact_NeutralAuxTargetAST)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The physical free-source refinement reads the original program and
its new terminal-cone test on the same tape. -/
theorem exact_OpenFreeAuxBranch (i : Program 1) (r : Program 3) (x w y : OTerm α)
    (free : Nonempty (Derivation B Γ (programGraph (atSource freeAux) (suc z) ![x,w,y])))
    (accept : Nonempty (Derivation B Γ (programGraph (neutralPositive i r) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (programGraph r (suc z) ![x,w,y] ⊓
      programGraph (freeAuxTarget i) (suc z) ![x,w,y])) := by
  rw [exact_NeutralPositiveAST] at accept
  exact conjunctionRecover r (freeAuxTarget i) ![x,w,y]
    (successorBranchElim (atSource freeAux) (refineAuxBottom i r) (conjunction r (freeAuxTarget i))
      (suc z) z ![x,w,y] free accept)

/-- Open the actual target test without reflecting numerals in an open
derivation. A whole-bottom candidate comes with the real scalar call
at that same y. An auxiliary target is recognized separately. -/
theorem exact_OpenFreeAuxTargetCases (i : Program 1) (x w y : OTerm α) (goal : Formula α)
    (accept : Nonempty (Derivation B Γ (programGraph (freeAuxTarget i) (suc z) ![x,w,y])))
    (aux : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ
        (programGraph bottomAuxTarget (suc z) ![x.relabel j,w.relabel j,y.relabel j])) →
      Nonempty (Derivation B Δ (goal.relabel j)))
    (bot : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ
        (programGraph bottomTarget (suc z) ![x.relabel j,w.relabel j,y.relabel j] ⊓
         programGraph (atTarget i) (suc z) ![x.relabel j,w.relabel j,y.relabel j])) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  rw [exact_NeutralAuxTargetAST] at accept
  apply optionGraphCases bottomTarget (![x,w,y] : Fin 3 → OTerm α) goal
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have held := renameInto accept j Δ keep
    simp only [programRename,tripleInputsRename,
      ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
      ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at held
    exact aux β j Δ keep (zeroBranchElim bottomTarget bottomAuxTarget
      (conjunction bottomTarget (atTarget i)) (suc z) ![x.relabel j,w.relabel j,y.relabel j] zero held)
  · intro β j Δ pred keep positive
    rw [tripleInputsRename] at positive
    have held := renameInto accept j Δ keep
    simp only [programRename,tripleInputsRename,
      ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
      ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at held
    apply bot β j Δ keep
    exact conjunctionRecover bottomTarget (atTarget i) ![x.relabel j,w.relabel j,y.relabel j]
      (successorBranchElim bottomTarget bottomAuxTarget (conjunction bottomTarget (atTarget i))
        (suc z) pred ![x.relabel j,w.relabel j,y.relabel j] positive held)

#print axioms exact_OpenFreeAuxBranch
#print axioms exact_OpenFreeAuxTargetCases
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementObjectBranchProof
