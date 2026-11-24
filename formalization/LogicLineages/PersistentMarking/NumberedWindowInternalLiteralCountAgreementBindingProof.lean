module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnSubst eqnRelabel)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountAllQueriesTargets

private theorem countedSubst {α β : Type} (list needle result : OTerm α) (σ : α → OTerm β) :
    (counted list needle result).subst (fun a => emb (σ a)) =
      counted (list.subst σ) (needle.subst σ) (result.subst σ) := by
  have tape : (fun i : Fin 2 => ((![list,needle] : Fin 2 → OTerm α) i).subst σ) =
      ![list.subst σ,needle.subst σ] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  simp only [counted,programSubst,tape]

private theorem matrixWitness {α : Type} (left right needle lc rc : OTerm α) :
    (agreementBody left right).subst (Sum.elim Term.var (fun i => emb (![needle,lc,rc] i))) =
      (counted left needle lc ⊓ counted right needle rc).imp (eqn lc rc) := by
  let ws : Fin 3 → OTerm α := ![needle,lc,rc]
  have he : (Sum.elim Term.var (fun i => emb (ws i))) =
      (fun a => emb (Sum.elim Term.var ws a)) := by
    funext a
    cases a <;> rfl
  change (agreementBody left right).subst (Sum.elim Term.var (fun i => emb (ws i))) = _
  rw [he]
  simp only [agreementBody,impSubst,conjunctionSubst,eqnSubst,countedSubst,witnessLift,
    Term.subst,Sum.elim_inr,ws] <;> rfl

theorem agreementRename {α β : Type} (left right : OTerm α) (j : α → β) :
    (agreement left right).relabel j = agreement (left.relabel j) (right.relabel j) := by
  unfold agreement
  rw [allBlockRename]
  have compose : ((Sum.map j id : α ⊕ Fin 3 → β ⊕ Fin 3) ∘ Sum.inl) = Sum.inl ∘ j := rfl
  simp only [agreementBody,impRename,conjunctionRename,countedRename,eqnRelabel,
    Term.relabel_relabel,compose,Term.relabel] <;> rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem agreementApply (left right needle lc rc : OTerm α)
    (h : Nonempty (Derivation B Γ (agreement left right)))
    (hl : Nonempty (Derivation B Γ (counted left needle lc)))
    (hr : Nonempty (Derivation B Γ (counted right needle rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  obtain ⟨paid⟩ := actualFiniteUniversalElimination B α 3 Γ (agreementBody left right)
    (fun i => emb (![needle,lc,rc] i)) h
  rw [matrixWitness] at paid
  obtain ⟨l⟩ := hl
  obtain ⟨r⟩ := hr
  exact ⟨Derivation.implicationElimination paid (Derivation.conjunctionIntroduction l r)⟩

#print axioms agreementApply
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
