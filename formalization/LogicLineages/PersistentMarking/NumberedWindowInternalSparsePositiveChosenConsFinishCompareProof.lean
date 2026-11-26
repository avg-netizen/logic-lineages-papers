module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFinishCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 equivalent)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)

attribute [local irreducible] programGraph finish

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveFinish (raw : Program 5) (least : Program 3)
    (out result ctx ty current cert next tail : OTerm α)
    (knownLeft : Nonempty (Derivation body Γ (finishGraph raw least result ctx ty current cert)))
    (knownRight : Nonempty (Derivation body Γ (finishGraph raw least result ctx ty next tail))) :
    Nonempty (Derivation body Γ ((finishGraph raw least out ctx ty current cert).imp
      (finishGraph raw least out ctx ty next tail))) := by
  obtain ⟨l⟩ := knownLeft
  obtain ⟨r⟩ := knownRight
  let lhs := finishGraph raw least out ctx ty current cert
  have input : Derivation body (lhs :: Γ) lhs := Derivation.hypothesis List.mem_cons_self
  have eq := valueUnique (finish raw least) result out (args4 ctx ty current cert)
    ⟨addHyp l lhs⟩ ⟨input⟩
  obtain ⟨output⟩ := outputTransport (finish raw least) result out (args4 ctx ty next tail)
    eq ⟨addHyp r lhs⟩
  exact ⟨Derivation.implicationIntroduction output⟩

theorem finishAtPair (raw : Program 5) (least : Program 3)
    (out state result ctx ty current cert next tail : OTerm α)
    (old : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty current cert)))
    (new : Nonempty (Derivation body Γ (loopGraph raw least state tail ctx ty next tail)))
    (done : Nonempty (Derivation body Γ (scratchGraph state z result))) :
    Nonempty (Derivation body Γ (equivalent (finishGraph raw least out ctx ty current cert)
      (finishGraph raw least out ctx ty next tail))) := by
  have l := terminalValue raw least state ctx ty current cert z result old done ⟨refl z⟩
  have r := terminalValue raw least state ctx ty next tail z result new done ⟨refl z⟩
  obtain ⟨f⟩ := moveFinish raw least out result ctx ty current cert next tail l r
  obtain ⟨b⟩ := moveFinish raw least out result ctx ty next tail current cert r l
  exact ⟨Derivation.conjunctionIntroduction f b⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFinishCompareProof
