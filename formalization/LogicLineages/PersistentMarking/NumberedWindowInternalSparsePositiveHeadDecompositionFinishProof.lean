module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputAcceptanceChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePositiveOutputGuardProof (nonemptyCode acceptNonempty)
open NumberedWindowInternalSparsePositiveOutputTestProof (compareTarget matchOfEqual)
open NumberedWindowInternalSparsePositiveOutputWalkProof (walkOfFinish)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveOpenCharacterizationTargets (successfulTerminal)
open NumberedWindowInternalSparsePositiveOpenCharacterizationChecks (exact_OpenPositiveCharacterization)
open NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof (targetCases)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem fromPositive (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (positive : Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (finishedNonempty raw least ctx ty source cert target)) := by
  obtain ⟨r⟩ := exact_OpenPositiveCharacterization body raw least α ctx ty source cert target
  obtain ⟨ok⟩ := positive
  have both := Derivation.implicationElimination (weakenClosed (Derivation.conjunctionLeft r) Γ) ok
  simp only [equalEqn] at both
  have nz : Nonempty (Derivation body Γ (eqn cert z).not) := ⟨Derivation.conjunctionLeft both⟩
  have state : Nonempty (Derivation body Γ (successfulTerminal raw least ctx ty source cert target)) :=
    ⟨Derivation.conjunctionRight both⟩
  apply targetCases raw least ctx ty source cert target (finishedNonempty raw least ctx ty source cert target) state
  intro β j Δ out hJ loop done
  rw [finishedRename]
  simp only [finishedNonempty,equalEqn]
  have n := renameInto nz j Δ hJ
  change Nonempty (Derivation body Δ ((eqn cert z).relabel j).not) at n
  rw [eqnRelabel,zRelabel] at n
  obtain ⟨nonzero⟩ := n
  obtain ⟨fin⟩ := terminalValue raw least out (ctx.relabel j) (ty.relabel j)
    (suc (source.relabel j)) (cert.relabel j) z (suc (target.relabel j)) loop done ⟨refl z⟩
  exact ⟨Derivation.conjunctionIntroduction nonzero fin⟩

theorem toPositive (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (known : Nonempty (Derivation body Γ (finishedNonempty raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target)) := by
  obtain ⟨known⟩ := known
  simp only [finishedNonempty,equalEqn] at known
  have nonzero : Nonempty (Derivation body Γ (eqn cert z).not) := ⟨Derivation.conjunctionLeft known⟩
  have walked := walkOfFinish raw least (suc target) ctx ty source cert target
    ⟨Derivation.conjunctionRight known⟩
  unfold positiveAt positive
  exact conjunctionAccept nonemptyCode (compareTarget raw least) (args5 ctx ty source cert target)
    (acceptNonempty ctx ty source cert target nonzero)
    (matchOfEqual raw least ctx ty source cert target (suc target) walked ⟨refl (suc target)⟩)

theorem positiveFinish : OpenPositiveFinish := by
  intro body raw least α ctx ty source cert target
  let a := positiveAt raw least ctx ty source cert target
  let b := finishedNonempty raw least ctx ty source cert target
  obtain ⟨f⟩ := fromPositive (body := body) (Γ := [a]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := toPositive (body := body) (Γ := [b]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof
