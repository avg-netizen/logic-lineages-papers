module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellProgramProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro successorBranchElim)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeTargets
open NumberedWindowInternalSparseDecodeSyntaxProof
open NumberedWindowInternalSparseFieldCell NumberedWindowInternalSparseFieldCellTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem attach (p : Program 1) (k out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out k))) :
    Nonempty (Derivation body Γ (unary (atPredecessor p) out (suc k))) := by
  apply compositionValue p (fun _ => predecessor) out ![suc k] ![k] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact predecessorSuccessor k

private theorem detach (p : Program 1) (k out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary (atPredecessor p) out (suc k)))) :
    Nonempty (Derivation body Γ (unary p out k)) := by
  apply compositionRecover p (fun _ => predecessor) out ![suc k] ![k] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact predecessorSuccessor k

theorem nilReject : Nonempty (Derivation body Γ (unary cellGood (z : OTerm α) z)) :=
  zeroBranchIntro (.projection 0) (constantZero 1) (atPredecessor good) z ![z]
    (projectionValue 0 ![z]) (zeroConstantValue ![z])

theorem setFlag (k out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary good out k))) :
    Nonempty (Derivation body Γ (unary cellGood out (suc k))) :=
  successorBranchIntro (.projection 0) (constantZero 1) (atPredecessor good) out k ![suc k]
    (projectionValue 0 ![suc k]) (attach good k out h)

theorem readFlag (k out : OTerm α)
    (h : Nonempty (Derivation body Γ (unary cellGood out (suc k)))) :
    Nonempty (Derivation body Γ (unary good out k)) :=
  detach good k out (successorBranchElim (.projection 0) (constantZero 1)
    (atPredecessor good) out k ![suc k] (projectionValue 0 ![suc k]) h)

theorem expandCell (k h t : OTerm α)
    (d : Nonempty (Derivation body Γ (certifiedCell (suc k) h t))) :
    Nonempty (Derivation body Γ (certifiedOutputs k h t)) := by
  obtain ⟨d⟩ := d
  obtain ⟨a⟩ := readFlag k (suc z) ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨b⟩ := detach leftCandidate k h ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
  obtain ⟨c⟩ := detach rightCandidate k t ⟨Derivation.conjunctionRight (Derivation.conjunctionRight d)⟩
  exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c)⟩

theorem contractCell (k h t : OTerm α)
    (d : Nonempty (Derivation body Γ (certifiedOutputs k h t))) :
    Nonempty (Derivation body Γ (certifiedCell (suc k) h t)) := by
  obtain ⟨d⟩ := d
  obtain ⟨a⟩ := setFlag k (suc z) ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨b⟩ := attach leftCandidate k h ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
  obtain ⟨c⟩ := attach rightCandidate k t ⟨Derivation.conjunctionRight (Derivation.conjunctionRight d)⟩
  exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellProgramProof
