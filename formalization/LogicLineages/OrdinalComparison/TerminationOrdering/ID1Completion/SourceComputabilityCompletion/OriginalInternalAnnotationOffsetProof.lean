module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationOffsetProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalSourceInversionSupportProof (onEquality)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (leftSuccessor)
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalSquareRootArithmeticSupportProof (orderLeft)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem cancelOrder (s t : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF (suc s) (suc t)))) :
 Nonempty (Derivation body Delta (ltF s t)) := by
 apply orderCases Delta (suc s) (suc t) _ h
 intro beta j Theta gap hj he
 simp only [orderRename]
 obtain ⟨he⟩ := he
 simp only [sucRelabel] at he
 apply actualOriginalOrderIntroduction body beta Theta (s.relabel j) (t.relabel j) gap
 rw [onEquality]
 exact ⟨cancelSuc (trans (symm (leftSuccessor (s.relabel j) (suc gap))) he)⟩
theorem notBelowBump (k : Nat) (cutoff : OTerm alpha) :
 Nonempty (Derivation body Delta (ltF (bump k cutoff) (numeral k)).not) := by
 induction k with
 | zero => exact InternalApplicationValidityStackAppendTransitionProof.notLessZero cutoff
 | succ k ih =>
   apply Nonempty.intro
   apply Derivation.implicationIntroduction
   have h : Nonempty (Derivation body (ltF (bump (k+1) cutoff) (numeral (k+1)) :: Delta)
     (ltF (suc (bump k cutoff)) (suc (numeral k)))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact Derivation.implicationElimination (Classical.choice (withHyp ih _))
    (Classical.choice (cancelOrder (bump k cutoff) (numeral k) h))
theorem shiftedNotBelow (k : Nat) (index cutoff : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn index (bump k cutoff)))) :
 Nonempty (Derivation body Delta (ltF index (numeral k)).not) := by
 apply Nonempty.intro
 apply Derivation.implicationIntroduction
 have h : Derivation body (ltF index (numeral k) :: Delta) (ltF index (numeral k)) :=
  Derivation.hypothesis List.mem_cons_self
 have ht := orderLeft (numeral k) (Classical.choice (withHyp he _)) h
 exact Derivation.implicationElimination (Classical.choice (withHyp (notBelowBump k cutoff) _)) ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationOffsetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationOffsetProof
