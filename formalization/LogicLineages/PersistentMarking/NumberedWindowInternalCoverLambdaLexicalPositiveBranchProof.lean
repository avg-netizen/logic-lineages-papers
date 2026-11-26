module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem byKnownValue (P C : Program 2) (x y res value : OTerm α) (Q : Formula α)
    (picked : Nonempty (Derivation body Γ
      (programGraph (branch P (constantZero 2) C) (suc res) ![x,y])))
    (control : Nonempty (Derivation body Γ (programGraph P value ![x,y])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph P (suc d) ![x.relabel j,y.relabel j])) →
      Nonempty (Derivation body Δ (programGraph C (suc (res.relabel j)) ![x.relabel j,y.relabel j])) →
      Nonempty (Derivation body Δ (Q.relabel j))) : Nonempty (Derivation body Γ Q) := by
  let E := eqn value z
  let xs : Fin 2 → OTerm α := ![x,y]
  apply zeroSuccessorCases Γ value Q
  · have zero : Nonempty (Derivation body (E :: Γ) (programGraph P z xs)) :=
      outputTransport P value z xs ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp control E)
    have impossible := zeroBranchElim P (constantZero 2) C (suc res) xs zero (withHyp picked E)
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc res) z xs impossible (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ d keep equal
    have ctl := renameInto control j Δ keep
    have found := renameInto picked j Δ keep
    simp only [programRename,binaryInputsRename,sucRelabel] at ctl found
    have good := outputTransport P (value.relabel j) (suc d) ![x.relabel j,y.relabel j] equal ctl
    have keepResult := successorBranchElim P (constantZero 2) C (suc (res.relabel j)) d
      ![x.relabel j,y.relabel j] good found
    exact next β j Δ d keep good keepResult

/-- Derive a genuine successor control, not an assumed positive result.
The zero branch cannot have the supplied nonzero observed output. -/
theorem positiveBranchCases (P C : Program 2) (x y res : OTerm α) (Q : Formula α)
    (picked : Nonempty (Derivation body Γ
      (programGraph (branch P (constantZero 2) C) (suc res) ![x,y])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph P (suc d) ![x.relabel j,y.relabel j])) →
      Nonempty (Derivation body Δ (programGraph C (suc (res.relabel j)) ![x.relabel j,y.relabel j])) →
      Nonempty (Derivation body Δ (Q.relabel j))) : Nonempty (Derivation body Γ Q) := by
  apply programCases P ![x,y] Q
  intro β j Δ value keep control
  rw [binaryInputsRename] at control
  have seen := renameInto picked j Δ keep
  simp only [programRename,binaryInputsRename,sucRelabel] at seen
  apply byKnownValue P C (x.relabel j) (y.relabel j) (res.relabel j) value (Q.relabel j) seen control
  intro γ k Ξ d retain good out
  have both : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at good out
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ d both good out

theorem unitCheckedBranch (P C : Program 2) (x y res : OTerm α)
    (actual : Nonempty (Derivation body Γ
      (programGraph (branch (normalize P) (constantZero 2) C) (suc res) ![x,y]))) :
    Nonempty (Derivation body Γ (programGraph P (suc z) ![x,y])) ∧
    Nonempty (Derivation body Γ (programGraph C (suc res) ![x,y])) := by
  let xs : Fin 2 → OTerm α := ![x,y]
  let F := programGraph P (suc z) xs
  have hit : Nonempty (Derivation body Γ F) := by
    apply formulaCases F F
    · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    · have zero := normalizeReject (body := body) (Gamma := F.not :: Γ) P xs
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have rejected := zeroBranchElim (normalize P) (constantZero 2) C (suc res) xs zero (withHyp actual F.not)
      obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc res) z xs rejected (constantZeroValue xs)
      exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  exact ⟨hit,successorBranchElim (normalize P) (constantZero 2) C (suc res) z xs
    (normalizeAccept P xs hit) actual⟩

#print axioms positiveBranchCases
#print axioms unitCheckedBranch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
