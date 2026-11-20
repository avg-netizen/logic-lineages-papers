module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalControlGraphProof (conditionalAtZero conditionalAtNonzero)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (branchValue)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)

attribute [local irreducible] programGraph

abbrev nonemptyCode : Program 5 := branch (.projection 3) (constantZero 5) (constantOne 5)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem emptyValue (ctx ty source cert target : OTerm α)
    (h0 : Nonempty (Derivation body Γ (eqn cert z))) :
    Nonempty (Derivation body Γ (programGraph nonemptyCode z (args5 ctx ty source cert target))) :=
  branchValue (.projection 3) (constantZero 5) (constantOne 5) z cert z (suc z)
    (args5 ctx ty source cert target) (projectionValue (3 : Fin 5) (args5 ctx ty source cert target))
    (zeroConstantValue (args5 ctx ty source cert target)) (oneConstantValue (args5 ctx ty source cert target))
    (conditionalAtZero cert z (suc z) h0)

theorem acceptNonempty (ctx ty source cert target : OTerm α)
    (hn : Nonempty (Derivation body Γ (eqn cert z).not)) :
    Nonempty (Derivation body Γ (programGraph nonemptyCode (suc z) (args5 ctx ty source cert target))) :=
  branchValue (.projection 3) (constantZero 5) (constantOne 5) (suc z) cert z (suc z)
    (args5 ctx ty source cert target) (projectionValue (3 : Fin 5) (args5 ctx ty source cert target))
    (zeroConstantValue (args5 ctx ty source cert target)) (oneConstantValue (args5 ctx ty source cert target))
    (conditionalAtNonzero cert z (suc z) hn)

theorem recoverNonempty (ctx ty source cert target : OTerm α)
    (selected : Nonempty (Derivation body Γ
      (programGraph nonemptyCode (suc z) (args5 ctx ty source cert target)))) :
    Nonempty (Derivation body Γ (eqn cert z).not) := by
  obtain ⟨d⟩ := selected
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  have empty := emptyValue (body := body) (Γ := eqn cert z :: Γ) ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨e⟩ := valueUnique nonemptyCode (suc z) z (args5 ctx ty source cert target)
    ⟨ID1Completion.InternalBetaTotalityProof.addHyp d (eqn cert z)⟩ empty
  exact sucNeZeroApply e

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputGuardProof
