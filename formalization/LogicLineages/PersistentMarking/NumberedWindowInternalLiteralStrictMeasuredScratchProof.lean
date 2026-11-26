module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredScratchProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof (exact_OpenSelectedGrammarAuxScratchMeasured)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof (exact_OpenUnrestrictedWindowFromSyntaxContext)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
  (exact_OpenUnrestrictedWindowReports exact_OpenUnrestrictedSyntaxWindowIntro)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverStrictAuxIntroduceProof (exact_OpenCoverStrictAuxIntroduce)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev measuredStrictCover (V TV baseM : Program 1) : Program 3 :=
  selectedCover (unitAuxSyntax V TV) (chosenMeasure baseM)

abbrev measuredStrictWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1) : Program 3 :=
  window (measuredStrictCover V TV baseM) s (strictAuxWindow base T) (unitAuxSyntax V TV)

/-- The original grammar computes the parent occurrence at the physical
scratch selected by the constructor. The actual type derivation is
produced by the strict auxiliary window, not the older fallback reader. -/
theorem exact_OpenStrictMeasuredAtScratch (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg p mf ma df bf da ba fState fTerms fArgs aState aTerms aArgs vertices : OTerm α) :
    let Va := unitAuxSyntax V TV
    let C := measuredStrictCover V TV baseM
    let W := measuredStrictWindow s base T V TV baseM
    let q := auxiliaryTerm dom cod fn arg
    D B Γ (windowAt W ctx (rawCons dom cod) fn) →
    D B Γ (windowAt W ctx dom arg) →
    MeasuredChild baseM s B Γ mf df bf fState fTerms fArgs fn →
    MeasuredChild baseM s B Γ ma da ba aState aTerms aArgs arg →
    D B Γ (programGraph chosenCombine p ![mf,ma]) →
    D B Γ (unary T (suc z) dom ⊓ unary T (suc z) cod) →
    D B Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod) →
    D B Γ (memberGraph (typesTerm s α) dom) →
    D B Γ (memberGraph (typesTerm s α) cod) →
    D B Γ (unary (scratchVertices C s) vertices q) →
    D B Γ (windowAt W ctx cod q) := by
  intro Va C W q fnHeld argHeld f a combine tw tv hd hc scratch
  let U := strictAuxWindow base T
  obtain ⟨fBits⟩ := exact_OpenUnrestrictedWindowReports C s U Va ctx (rawCons dom cod) fn fnHeld
  obtain ⟨aBits⟩ := exact_OpenUnrestrictedWindowReports C s U Va ctx dom arg argHeld
  obtain ⟨syntaxTypes⟩ := tv
  have syntaxParent : D B Γ (unary Va (suc z) q) :=
    exact_OpenUnitAuxSyntaxIntro V TV B α Γ dom cod fn arg
      ⟨Derivation.conjunctionLeft syntaxTypes⟩ ⟨Derivation.conjunctionRight syntaxTypes⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fBits)⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight aBits)⟩
  have own := exact_OpenSelectedGrammarAuxScratchMeasured Va baseM s B α Γ p mf ma
    df bf da ba fState fTerms fArgs aState aTerms aArgs vertices dom cod fn arg
    f a combine hd hc syntaxParent scratch
  obtain ⟨types⟩ := tw
  have typeParent : D B Γ (windowAt U ctx cod q) :=
    exact_OpenCoverStrictAuxIntroduce base T B α Γ ctx dom cod fn arg
      ⟨Derivation.conjunctionIntroduction types (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft fBits) (Derivation.conjunctionLeft aBits))⟩
  have both := exact_OpenUnrestrictedSyntaxWindowIntro U Va ctx cod q typeParent syntaxParent
  exact exact_OpenUnrestrictedWindowFromSyntaxContext C s U Va ctx (rawCons dom cod) fn cod q vertices
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight fBits)⟩ both scratch own

#print axioms exact_OpenStrictMeasuredAtScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredScratchProof
