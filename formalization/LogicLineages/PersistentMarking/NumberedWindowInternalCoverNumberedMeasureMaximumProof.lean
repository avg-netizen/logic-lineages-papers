module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureMaximumProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn emb bindEmbedding liftBind varBind sucSubst)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addZero addSucc congSuc)
open ID1Completion.InternalAdditionLawsProof (add addSubst)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess rejectOfNotLess)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalQuotientComparisonProof (actualOriginalComparison compareView)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight rightSuccessor)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalChosenAuxMeasureCombine
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
open NumberedWindowInternalCoverNumberedMeasureCombineTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selfWeak (n : OTerm α) : Nonempty (Derivation body Γ (ltF n (suc n))) := by
  apply actualOriginalOrderIntroduction body α Γ n (suc n) z
  rw [onEquality]
  exact ⟨trans (addSucc n z) (congSuc (addZero n))⟩

private theorem reverseWeak (a b : OTerm α) (notLess : Derivation body Γ (ltF a b).not) :
    Nonempty (Derivation body Γ (ltF b (suc a))) := by
  let L := ltF a b
  let E := eqn a b
  let R := ltF b a
  let goal := ltF b (suc a)
  obtain ⟨law⟩ := actualOriginalComparison body α a b
  have order := compareView (weakenClosed law Γ)
  have fail : Derivation body Γ (L.imp goal) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp notLess L)
      (Derivation.hypothesis List.mem_cons_self)))
  obtain ⟨same⟩ := selfWeak (body := body) (Γ := E :: Γ) b
  have equal : Derivation body Γ (E.imp goal) := Derivation.implicationIntroduction
    (orderRight b (congSuc (symm (Derivation.hypothesis List.mem_cons_self))) same)
  obtain ⟨greater⟩ := rightSuccessor (body := body) (Gamma := R :: Γ) b a
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have reverse : Derivation body Γ (R.imp goal) := Derivation.implicationIntroduction greater
  have rest : Derivation body Γ ((E ⊔ R).imp goal) := Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp equal (E ⊔ R)) (addHyp reverse (E ⊔ R)))
  exact ⟨disjunctionElimination order fail rest⟩

theorem exact_OpenCoverMaximumWeak : ExactOpenCoverMaximumWeak := by
  intro body α Γ a b w observed
  let L := ltF a b
  apply formulaCases L _
  · have less : Nonempty (Derivation body (L :: Γ) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have selected : Nonempty (Derivation body (L :: Γ) (programGraph maximum b ![a,b])) :=
      successorBranchIntro ID1Completion.InternalLessThan.ltTest (.projection 0) (.projection 1)
        b z ![a,b] (acceptOfLess a b less) (projectionValue 1 ![a,b])
    obtain ⟨same⟩ := valueUnique maximum b w ![a,b] selected (withHyp observed L)
    obtain ⟨left⟩ := rightSuccessor a b less
    obtain ⟨right⟩ := selfWeak (body := body) (Γ := L :: Γ) b
    exact ⟨Derivation.conjunctionIntroduction
      (orderRight a (congSuc same) left) (orderRight b (congSuc same) right)⟩
  · have negate : Derivation body (L.not :: Γ) L.not := Derivation.hypothesis List.mem_cons_self
    have selected : Nonempty (Derivation body (L.not :: Γ) (programGraph maximum a ![a,b])) :=
      zeroBranchIntro ID1Completion.InternalLessThan.ltTest (.projection 0) (.projection 1)
        a ![a,b] (rejectOfNotLess a b ⟨negate⟩) (projectionValue 0 ![a,b])
    obtain ⟨same⟩ := valueUnique maximum a w ![a,b] selected (withHyp observed L.not)
    obtain ⟨left⟩ := selfWeak (body := body) (Γ := L.not :: Γ) a
    obtain ⟨right⟩ := reverseWeak a b negate
    exact ⟨Derivation.conjunctionIntroduction
      (orderRight a (congSuc same) left) (orderRight b (congSuc same) right)⟩

#print axioms exact_OpenCoverMaximumWeak

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureMaximumProof
