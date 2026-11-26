module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixBypassProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixRawFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixNonLambdaProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof (equalityReject)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaHeadTest lambdaWitnessTest)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixRawFitProof (prefixRaw exact_OpenPrefixRaw)
open NumberedWindowInternalLiteralLambdaPrefixBypassProof (exact_OpenPrefixStops)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixNoLambdaHead (c t q w r tag : OTerm α)
    (tagged : D B Γ (unary cellHead tag q))
    (notLambda : D B Γ (eqn tag (numeral 2 : OTerm α)).not) :
    D B Γ (programGraph isLambdaPrefix z ![c,t,q,w,r]) := by
  let gate : Program 1 := .composition equalityTest ![cellHead,literal 1 2]
  have checked : D B Γ (unary gate z q) := by
    apply compositionValue equalityTest ![cellHead,literal 1 2] z ![q] ![tag,numeral 2]
      (equalityReject tag (numeral 2) notLambda)
    intro i
    exact Fin.cases tagged (Fin.cases (literalGraph 2 ![q]) (fun e => Fin.elim0 e)) i
  have off : D B Γ (programGraph lambdaHeadTest z ![q,w,r]) := onTape gate 0 z ![q,w,r] checked
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  have zero : D B Γ (programGraph (rawTripleCall lambdaHeadTest) z xs) := by
    apply compositionValue lambdaHeadTest ![.projection 2,.projection 3,.projection 4] z xs ![q,w,r] off
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (fun e => Fin.elim0 e))) i
  let p := rawTripleCall lambdaHeadTest
  let A := bit5 p xs
  obtain ⟨z₀⟩ := zero
  have bad : D B Γ A.not := by
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have unequal := valueUnique p (suc z) z xs ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp z₀ A⟩
    exact sucNeZeroApply (Classical.choice unequal)
  unfold isLambdaPrefix conjunction
  exact zeroBranchIntro _ (constantZero 5) _ z xs (normalizeReject _ xs bad) (constantZeroValue xs)

/-- Non-lambda frontiers pay no lexical-prefix obligations. In
particular the same actual typed root/copy/auxiliary step can be
introduced at its unchanged certificate and target. -/
theorem exact_OpenPrefixRawNonLambda (W : Program 3) (raw : Program 5) (c t q w r tag : OTerm α)
    (tagged : D B Γ (unary cellHead tag q))
    (notLambda : D B Γ (eqn tag (numeral 2 : OTerm α)).not)
    (held : D B Γ (programGraph raw (suc z) ![c,t,q,w,r])) :
    D B Γ (programGraph (prefixRaw W raw) (suc z) ![c,t,q,w,r]) :=
  (exact_OpenPrefixRaw W raw ![c,t,q,w,r]).mpr
    ⟨held,exact_OpenPrefixStops W c t q w r (exact_OpenPrefixNoLambdaHead c t q w r tag tagged notLambda)⟩

theorem exact_OpenPrefixRawAuxiliary (W : Program 3) (raw : Program 5) (c t d k fn arg w r : OTerm α)
    (held : D B Γ (programGraph raw (suc z) ![c,t,auxiliaryTerm d k fn arg,w,r])) :
    D B Γ (programGraph (prefixRaw W raw) (suc z) ![c,t,auxiliaryTerm d k fn arg,w,r]) := by
  obtain ⟨known⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 6) (packedBody [d,k,fn,arg])
  have tag : D B Γ (unary cellHead (numeral 6) (auxiliaryTerm d k fn arg)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight known)⟩
  have off : D B Γ (eqn (numeral 6 : OTerm α) (numeral 2)).not := by
    exact ⟨Derivation.implicationIntroduction
      (numeralNeApply 6 2 (by decide) (Derivation.hypothesis List.mem_cons_self))⟩
  exact exact_OpenPrefixRawNonLambda W raw c t (auxiliaryTerm d k fn arg) w r (numeral 6) tag off held

#print axioms exact_OpenPrefixNoLambdaHead
#print axioms exact_OpenPrefixRawNonLambda
#print axioms exact_OpenPrefixRawAuxiliary
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixNonLambdaProof
