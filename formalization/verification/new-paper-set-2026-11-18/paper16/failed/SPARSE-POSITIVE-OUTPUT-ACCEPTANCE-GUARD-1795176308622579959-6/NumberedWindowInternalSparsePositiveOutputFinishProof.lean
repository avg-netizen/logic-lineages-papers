module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputScratchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalControlGraphProof (conditionalAtZero conditionalAtNonzero)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (branchValue)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalListCodec (headCode tailCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFold (chosenState finish)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveOutputTargets
open NumberedWindowInternalSparsePositiveOutputScratchProof (atState scratchParts)

attribute [local irreducible] programGraph chosenState

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem terminalValue (raw : Program 5) (least : Program 3)
    (state ctx ty initial certificate cursor current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state certificate ctx ty initial certificate)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state cursor current)))
    (done : Nonempty (Derivation body Γ (eqn cursor z))) :
    Nonempty (Derivation body Γ
      (programGraph (finish raw least) current (args4 ctx ty initial certificate))) := by
  obtain ⟨parts⟩ := scratchParts raw least state ctx ty initial certificate cursor current loop pair
  unfold finish
  exact branchValue (atState raw least headCode) (atState raw least tailCode) (constantZero 4)
    current cursor current z (args4 ctx ty initial certificate)
    ⟨Derivation.conjunctionLeft parts⟩ ⟨Derivation.conjunctionRight parts⟩
    (zeroConstantValue (args4 ctx ty initial certificate)) (conditionalAtZero cursor current z done)

theorem nonterminalValue (raw : Program 5) (least : Program 3)
    (state ctx ty initial certificate cursor current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state certificate ctx ty initial certificate)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state cursor current)))
    (notDone : Nonempty (Derivation body Γ (eqn cursor z).not)) :
    Nonempty (Derivation body Γ
      (programGraph (finish raw least) z (args4 ctx ty initial certificate))) := by
  obtain ⟨parts⟩ := scratchParts raw least state ctx ty initial certificate cursor current loop pair
  unfold finish
  exact branchValue (atState raw least headCode) (atState raw least tailCode) (constantZero 4)
    z cursor current z (args4 ctx ty initial certificate)
    ⟨Derivation.conjunctionLeft parts⟩ ⟨Derivation.conjunctionRight parts⟩
    (zeroConstantValue (args4 ctx ty initial certificate)) (conditionalAtNonzero cursor current z notDone)

theorem atScratch : OpenFinishAtScratch := by
  intro body raw least α state ctx ty initial cert cursor current
  simp only [equalEqn]
  let given := loopGraph raw least state cert ctx ty initial cert ⊓ scratchGraph state cursor current
  let yes := eqn cursor z
  have h : Derivation body [given] given := Derivation.hypothesis List.mem_cons_self
  obtain ⟨v⟩ := terminalValue (Γ := yes :: [given]) raw least state ctx ty initial cert cursor current
    ⟨Derivation.conjunctionLeft (addHyp h yes)⟩ ⟨Derivation.conjunctionRight (addHyp h yes)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨u⟩ := nonterminalValue (Γ := yes.not :: [given]) raw least state ctx ty initial cert cursor current
    ⟨Derivation.conjunctionLeft (addHyp h yes.not)⟩ ⟨Derivation.conjunctionRight (addHyp h yes.not)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction v)
      (Derivation.implicationIntroduction u))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
