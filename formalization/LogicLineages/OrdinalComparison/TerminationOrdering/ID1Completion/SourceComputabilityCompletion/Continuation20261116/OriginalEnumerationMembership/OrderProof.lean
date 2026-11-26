module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm trans cancelSuc)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalOrderProof
open InternalAdditionLawsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem successorForward (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess a b))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess (suc a) (suc b))) :=
  OriginalApplicationSpinePrefixCoreProof.successorLess a b h

theorem successorBackward (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess (suc a) (suc b)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess a b)) := by
  apply orderCases Delta (suc a) (suc b) _ h
  intro beta j Theta gap hj he
  simp only [InternalLessThan.strictLess,orderRename]
  simp only [InternalTagArithmeticSyntaxProof.sucRelabel] at he
  apply actualOriginalOrderIntroduction body beta Theta (a.relabel j) (b.relabel j) gap
  rw [InternalSourceInversionSupportProof.onEquality]
  exact ⟨cancelSuc (trans (symm (leftSuccessor (a.relabel j) (suc gap))) (Classical.choice he))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
