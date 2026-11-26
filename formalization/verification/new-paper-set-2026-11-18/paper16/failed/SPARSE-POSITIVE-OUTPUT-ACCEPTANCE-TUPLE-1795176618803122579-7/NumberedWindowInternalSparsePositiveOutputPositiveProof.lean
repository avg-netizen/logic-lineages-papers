module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputPositiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (chosenWalk positive)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveOutputTargets
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveOutputWalkProof (walkOfFinish)
open NumberedWindowInternalSparsePositiveOutputGuardProof
open NumberedWindowInternalSparsePositiveOutputTestProof

attribute [local irreducible] programGraph chosenWalk

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem authorize (raw : Program 5) (least : Program 3)
    (state ctx ty source cert target current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph state z current)))
    (nonzero : Nonempty (Derivation body Γ (eqn cert z).not))
    (eq : Nonempty (Derivation body Γ (eqn current (suc target)))) :
    Nonempty (Derivation body Γ
      (programGraph (positive raw least) (suc z) (args5 ctx ty source cert target))) := by
  have finished := terminalValue raw least state ctx ty (suc source) cert z current loop done ⟨refl z⟩
  have walk := walkOfFinish raw least current ctx ty source cert target finished
  unfold positive
  exact conjunctionAccept nonemptyCode (compareTarget raw least) (args5 ctx ty source cert target)
    (acceptNonempty ctx ty source cert target nonzero)
    (matchOfEqual raw least ctx ty source cert target current walk eq)

private theorem readAcceptance (raw : Program 5) (least : Program 3)
    (state ctx ty source cert target current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert)))
    (done : Nonempty (Derivation body Γ (scratchGraph state z current)))
    (ok : Nonempty (Derivation body Γ
      (programGraph (positive raw least) (suc z) (args5 ctx ty source cert target)))) :
    Nonempty (Derivation body Γ ((eqn cert z).not ⊓ eqn current (suc target))) := by
  have finished := terminalValue raw least state ctx ty (suc source) cert z current loop done ⟨refl z⟩
  have walk := walkOfFinish raw least current ctx ty source cert target finished
  unfold positive at ok
  obtain ⟨both⟩ := conjunctionRecover nonemptyCode (compareTarget raw least)
    (args5 ctx ty source cert target) ok
  obtain ⟨hne⟩ := recoverNonempty ctx ty source cert target ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨he⟩ := equalOfMatch raw least ctx ty source cert target current walk
    ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.conjunctionIntroduction hne he⟩

theorem atTerminal : OpenPositiveAtTerminal := by
  intro body raw least α state ctx ty source cert target current
  simp only [equalEqn]
  let done := loopGraph raw least state cert ctx ty (suc source) cert ⊓ scratchGraph state z current
  let ok := programGraph (positive raw least) (suc z) (args5 ctx ty source cert target)
  let valid := (eqn cert z).not ⊓ eqn current (suc target)
  have h : Derivation body [done] done := Derivation.hypothesis List.mem_cons_self
  have v : Derivation body [valid,done] valid := Derivation.hypothesis List.mem_cons_self
  obtain ⟨yes⟩ := readAcceptance (Γ := [ok,done]) raw least state ctx ty source cert target current
    ⟨Derivation.conjunctionLeft (addHyp h ok)⟩ ⟨Derivation.conjunctionRight (addHyp h ok)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨back⟩ := authorize (Γ := [valid,done]) raw least state ctx ty source cert target current
    ⟨Derivation.conjunctionLeft (addHyp h valid)⟩ ⟨Derivation.conjunctionRight (addHyp h valid)⟩
    ⟨Derivation.conjunctionLeft v⟩ ⟨Derivation.conjunctionRight v⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction back))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputPositiveProof
