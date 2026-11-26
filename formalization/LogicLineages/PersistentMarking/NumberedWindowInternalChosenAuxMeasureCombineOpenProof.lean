module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombinePairProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenProof
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
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
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
open NumberedWindowInternalChosenAuxMeasureCombinePairProof (pairFromCombine)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairSubst {α β : Type} (p d b : OTerm α) (ts : α → OTerm β) :
    (codePair p d b).subst (fun i => emb (ts i)) =
      codePair (p.subst ts) (d.subst ts) (b.subst ts) := by
  have tape : (fun i => ((![d,b] : Fin 2 → OTerm α) i).subst ts) = ![d.subst ts,b.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  unfold codePair
  rw [programSubst,tape]

private theorem bindReport {α : Type} (p df da bf ba b : OTerm α) :
    instantiate (boundBody p df da bf ba) (emb b) = boundReport p df da bf ba b := by
  rw [instantiate,bindEmbedding]
  simp only [boundBody,boundReport,conjunctionSubst,pairSubst,orderSubst,sucSubst,addSubst,liftBind,varBind]

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

private theorem withBound (p mf ma df da bf ba b : OTerm α)
    (hf : Nonempty (Derivation body Γ (codePair mf df bf)))
    (ha : Nonempty (Derivation body Γ (codePair ma da ba)))
    (out : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])))
    (choice : Nonempty (Derivation body Γ (programGraph maximum b ![bf,ba])))
    (wf : Nonempty (Derivation body Γ (ltF bf (suc b))))
    (wa : Nonempty (Derivation body Γ (ltF ba (suc b)))) :
    Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba))) := by
  obtain ⟨paired⟩ := pairFromCombine p mf ma df da bf ba b hf ha out choice
  obtain ⟨fd⟩ := leftWeakAdd (body := body) (Gamma := Γ) df da
  obtain ⟨ad⟩ := rightWeakAdd (body := body) (Gamma := Γ) df da
  obtain ⟨wf⟩ := wf
  obtain ⟨wa⟩ := wa
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb b)
  rw [bindReport]
  exact Derivation.conjunctionIntroduction paired
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction fd ad)
      (Derivation.conjunctionIntroduction wf wa))

theorem exact_OpenChosenAuxMeasureCombine : ExactOpenChosenAuxMeasureCombine := by
  intro body α Γ p mf ma df da bf ba hf ha out
  let L := ltF bf ba
  apply formulaCases L _
  · have less : Nonempty (Derivation body (L :: Γ) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have selected : Nonempty (Derivation body (L :: Γ) (programGraph maximum ba ![bf,ba])) :=
      successorBranchIntro ID1Completion.InternalLessThan.ltTest (.projection 0) (.projection 1)
        ba z ![bf,ba] (acceptOfLess bf ba less) (projectionValue 1 ![bf,ba])
    exact withBound p mf ma df da bf ba ba (withHyp hf L) (withHyp ha L) (withHyp out L)
      selected (rightSuccessor bf ba less) (selfWeak ba)
  · have notLess : Derivation body (L.not :: Γ) L.not := Derivation.hypothesis List.mem_cons_self
    have selected : Nonempty (Derivation body (L.not :: Γ) (programGraph maximum bf ![bf,ba])) :=
      zeroBranchIntro ID1Completion.InternalLessThan.ltTest (.projection 0) (.projection 1)
        bf ![bf,ba] (rejectOfNotLess bf ba ⟨notLess⟩) (projectionValue 0 ![bf,ba])
    exact withBound p mf ma df da bf ba bf (withHyp hf L.not) (withHyp ha L.not) (withHyp out L.not)
      selected (selfWeak bf) (reverseWeak bf ba notLess)

#print axioms exact_OpenChosenAuxMeasureCombine

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenProof
