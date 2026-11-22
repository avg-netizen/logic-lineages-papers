module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalLessThan (constantOne ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess oneConstantValue)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalEqualityTestSubtractionProof (diagonal)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrame (frameGood frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof (literalTape)
open NumberedWindowInternalSparsePair (pair pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph)
open NumberedWindowInternalAuxExchangeMemoStepTargets
open NumberedWindowInternalAuxExchangeMemoOpenStepTargets
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof

theorem exact_OpenAuxMemoStepAtGap : ExactOpenAuxMemoStepAtGap := by
  intro base V body α Γ dom cod fn fn' arg gap old keyEq syntaxSrc syntaxDst priorLookup
  let src := auxiliaryTerm dom cod fn arg
  let dst := auxiliaryTerm dom cod fn' arg
  let child := pairTerm fn fn'
  let parent := pairTerm src dst
  let prior := OrdinaryArithmetic.addTerm child gap
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have reports := keyReports (body := body) (Γ := Γ) prior old src dst keyEq
  have frame := literalTape (body := body) (Γ := Γ) dom cod arg fn z fn'
  have fromFrame := frameGraph frameGood (suc z) src dst xs reports frame.guard
  have fromSource := frameGraph (frameSlot 2 0) fn src dst xs reports frame.source
  have fromTarget := frameGraph (frameSlot 2 2) fn' src dst xs reports frame.target
  have paired : Nonempty (Derivation body Γ (programGraph childKey child xs)) :=
    binaryGraph pair (atFrame (frameSlot 2 0)) (atFrame (frameSlot 2 2)) child fn fn' xs
      (pairGraph fn fn') fromSource fromTarget
  have below : Nonempty (Derivation body Γ (ltF child parent)) := by
    obtain ⟨e⟩ := keyEq
    obtain ⟨h⟩ := leftWeakAdd (body := body) (Gamma := Γ) child gap
    exact ⟨orderRight child e h⟩
  have earlier : Nonempty (Derivation body Γ (programGraph childEarlier (suc z) xs)) :=
    binaryGraph ltTest childKey currentKey (suc z) child parent xs
      (acceptOfLess child parent below) paired reports.current
  have difference : Nonempty (Derivation body Γ (programGraph childLag gap xs)) :=
    binaryGraph subtract childKey (.projection 0) gap child prior xs
      (diagonal child gap) paired (projectionValue 0 xs)
  have read : Nonempty (Derivation body Γ (programGraph childResult (suc z) xs)) :=
    binaryGraph lookup childLag (.projection 1) (suc z) gap old xs
      priorLookup difference (projectionValue (1 : Fin 4) xs)
  have srcGood := unaryGraph V rawSource (suc z) src xs syntaxSrc reports.source
  have dstGood := unaryGraph V rawTarget (suc z) dst xs syntaxDst reports.target
  have branches : Nonempty (Derivation body Γ (programGraph (enough V) (suc z) xs)) :=
    conjunctionAccept (atFrame frameGood) _ xs fromFrame
      (conjunctionAccept (unaryAfter V rawSource) _ xs srcGood
        (conjunctionAccept (unaryAfter V rawTarget) _ xs dstGood
          (conjunctionAccept childEarlier childResult xs earlier read)))
  have inner := successorBranchIntro (enough V) (binaryAfter base rawSource rawTarget)
    (constantOne 4) (suc z) z xs branches (oneConstantValue xs)
  exact successorBranchIntro goodKey (constantZero 4)
    (branch (enough V) (binaryAfter base rawSource rawTarget) (constantOne 4))
    (suc z) z xs reports.valid inner

#print axioms exact_OpenAuxMemoStepAtGap

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepChecks
