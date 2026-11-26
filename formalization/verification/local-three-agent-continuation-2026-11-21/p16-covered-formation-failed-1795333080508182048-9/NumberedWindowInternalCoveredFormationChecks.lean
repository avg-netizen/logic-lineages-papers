module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseCoveredWindowTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
open NumberedWindowInternalOwnCoverReportsTargets
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall generatorCall)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape)
open NumberedWindowInternalSparseCoverScratchOpenChecks (exact_ScratchCallbackZero)
open NumberedWindowInternalSparseCoverOccurrenceTargets (coverRow)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open SourceComputabilityFormulaSupportProof (existsOne)
open List.Vector


open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseStructuralApplicationTargets (window syntaxWindow)
open NumberedWindowInternalCoveredFormationTargets
open NumberedWindowInternalOwnCoverReportsChecks (exact_OwnCoverReports)
open NumberedWindowInternalAuxWindowOpenChecks (exact_OpenAuxWindow)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

private theorem atContext (out ctx ty term : OTerm α)
    (parsed : Nonempty (Derivation body Γ (unary parser out ctx))) :
    Nonempty (Derivation body Γ (programGraph contextOption out ![ctx,ty,term])) := by
  apply compositionValue parser (fun _ : Fin 1 => .projection 0) out ![ctx,ty,term] ![ctx] parsed
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 _

private theorem moveContext (ctx ty src newTy dst : OTerm α)
    (present : Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx,ty,src]))) :
    Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx,newTy,dst])) := by
  apply optionGraphCases parser (![ctx] : Fin 1 → OTerm α) _
  · intro β j Δ keep zero
    rw [unaryInputsRename] at zero
    have old := renameInto present j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at old
    let xs := ![ctx.relabel j,ty.relabel j,src.relabel j]
    have miss := atContext z (ctx.relabel j) (ty.relabel j) (src.relabel j) zero
    have invalid := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs miss old
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs invalid (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ witness keep parsed
    rw [unaryInputsRename] at parsed
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    let xs := ![ctx.relabel j,newTy.relabel j,dst.relabel j]
    have moved := atContext (suc witness) (ctx.relabel j) (newTy.relabel j) (dst.relabel j) parsed
    exact successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) witness xs moved (oneConstantValue xs)

theorem exact_CoveredFormation : ExactCoveredFormation := by
  intro baseV M G s intrinsicBase T body α Γ ctx dom cod f arg V C K W parent types children
  let input := (types ⊓ children) ⊓ occursInCover C s parent parent
  let Δ := input :: Γ
  have h : Derivation body Δ input := Derivation.hypothesis List.mem_cons_self
  have parts := Derivation.conjunctionLeft h
  have both := Derivation.conjunctionRight parts
  let fTape := ![ctx,rawCons dom cod,f]
  let aTape := ![ctx,dom,arg]
  let pTape := ![ctx,cod,parent]
  let extra := conjunction contextPresent (ownSeed C s)
  obtain ⟨fr⟩ := conjunctionRecover (syntaxWindow K V) extra fTape ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨ar⟩ := conjunctionRecover (syntaxWindow K V) extra aTape ⟨Derivation.conjunctionRight both⟩
  obtain ⟨fc⟩ := conjunctionRecover K (rawCall V) fTape ⟨Derivation.conjunctionLeft fr⟩
  obtain ⟨ac⟩ := conjunctionRecover K (rawCall V) aTape ⟨Derivation.conjunctionLeft ar⟩
  obtain ⟨context⟩ := conjunctionRecover contextPresent (ownSeed C s) fTape ⟨Derivation.conjunctionRight fr⟩
  have moved := moveContext ctx (rawCons dom cod) f cod parent ⟨Derivation.conjunctionLeft context⟩
  obtain ⟨aux⟩ := exact_OpenAuxWindow intrinsicBase T body α Δ ctx dom cod f arg
  have formed := Derivation.implicationElimination aux (Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft parts) (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft fc) (Derivation.conjunctionLeft ac)))
  obtain ⟨report⟩ := exact_OwnCoverReports baseV M G s body α Δ ctx cod parent
  have guard := Derivation.implicationElimination report (Derivation.conjunctionRight h)
  have syntaxRun : Nonempty (Derivation body Δ (programGraph (rawCall V) (suc z) pTape)) := by
    apply compositionValue V (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) pTape ![parent] ⟨Derivation.conjunctionLeft guard⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 pTape
  have typed := conjunctionAccept K (rawCall V) pTape ⟨formed⟩ syntaxRun
  have extraRun := conjunctionAccept contextPresent (ownSeed C s) pTape moved ⟨Derivation.conjunctionRight guard⟩
  obtain ⟨result⟩ := conjunctionAccept (syntaxWindow K V) extra pTape typed extraRun
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_CoveredFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationChecks
