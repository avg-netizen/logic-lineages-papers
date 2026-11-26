module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans congSuc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalAdditionLawsProof (add leftSuccessor)
open ID1Completion.InternalAdditionCancellationProof (commutativity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxExchangeKeyChecks (exact_OpenAuxFunctionKeyDecrease)
open NumberedWindowInternalAuxExchangeMemoLiftTargets
open NumberedWindowInternalAuxExchangeMemoThinLiftGapProof (pairRelabel atGap)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem derive (base : Program 2) (V : Program 1) (dom cod fn fn' arg : OTerm α)
    (child : Nonempty (Derivation body Γ (accepts base V fn fn')))
    (checkSrc : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn arg))))
    (checkDst : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn' arg)))) :
    Nonempty (Derivation body Γ (accepts base V (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))) := by
  let src := auxiliaryTerm dom cod fn arg
  let dst := auxiliaryTerm dom cod fn' arg
  let childKey := pairTerm fn fn'
  let parentKey := pairTerm src dst
  have strict := exact_OpenAuxFunctionKeyDecrease body α Γ dom cod fn fn' arg
  apply orderCases Γ childKey parentKey _ strict
  intro β j Δ gap hJ equation
  simp only [accepts,programRename,binaryInputsRename,sucRelabel,zRelabel,auxiliaryRename]
  have raw := renameInto child j Δ hJ
  have left := renameInto checkSrc j Δ hJ
  have right := renameInto checkDst j Δ hJ
  simp only [accepts,programRename,binaryInputsRename,sucRelabel,zRelabel] at raw
  change Nonempty (Derivation body Δ ((unary V (suc z) (auxiliaryTerm dom cod fn arg)).relabel j)) at left
  change Nonempty (Derivation body Δ ((unary V (suc z) (auxiliaryTerm dom cod fn' arg)).relabel j)) at right
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at left right
  simp only [childKey,parentKey,src,dst,pairRelabel,auxiliaryRename] at equation
  obtain ⟨rebuild⟩ := equation
  let lo := pairTerm (fn.relabel j) (fn'.relabel j)
  have addSucc : Derivation body Δ (eqn (add lo (suc gap)) (suc (add lo gap))) :=
    trans (commutativity lo (suc gap)) (trans (leftSuccessor gap lo) (congSuc (commutativity gap lo)))
  exact atGap base V (dom.relabel j) (cod.relabel j) (fn.relabel j) (fn'.relabel j) (arg.relabel j) gap
    ⟨trans (symm addSucc) rebuild⟩ raw left right

theorem exact_OpenAuxMemoFunctionLift : ExactOpenAuxMemoFunctionLift := by
  intro base V body α Γ dom cod fn fn' arg a b
  let h := accepts base V fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)
  have input : Derivation body (h :: Γ) h := Derivation.hypothesis List.mem_cons_self
  obtain ⟨out⟩ := derive base V dom cod fn fn' arg ⟨Derivation.conjunctionLeft input⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight input)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight input)⟩
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenAuxMemoFunctionLift

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftChecks
