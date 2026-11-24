module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSplitSideIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountReflexiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepAssembleProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn projectionValue)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalRawListRecursionProof (consValue nilValue)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm guardAt reports)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalOriginalRawConsUnionReportThinProof
  (actualRawConsParser OpenObserverReflexivity)
open NumberedWindowInternalDirectInsertedIntroProof
open NumberedWindowInternalDirectInsertedScan (exactOpenScanNil)
open NumberedWindowInternalDirectTargetMapLocalIntroProof
  (exact_OpenTargetProjectionNil exact_OpenTargetProjectionStepIntro exact_OpenRawTargetProjectionIntro)
open NumberedWindowInternalDirectInsertedTargetsMapTargets
  (scratchTargets targetBase targetStep insertedTargets)
open NumberedWindowInternalDirectTypedScratchIntroProof (exact_TypedScratchNil exact_IntroTypedScratchCons)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalLiteralCountReflexiveProof (exact_LiteralObserverReflexivity)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectSplitSideIntroProof
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
abbrev D (p : Formula α) := Nonempty (Derivation B Γ p)

def singletonRow {α : Type} (x w y : OTerm α) : OTerm α :=
  tripleTerm 4 y x w

def singletonWitness {α : Type} (x w y : OTerm α) : OTerm α :=
  tripleTerm 5 z (singletonCode x) (rawCons (singletonRow x w y) z)

private theorem leftNil (n : OTerm α) :
    D (B := B) (Γ := Γ) (programGraph append n ![z,n]) :=
  nilValue (.projection 0) appendStep n ![n] (projectionValue 0 ![n])

private theorem singletonProjection (x w y rows ys : OTerm α)
    (new : D (B := B) (Γ := Γ) (consGraph ys y z))
    (oneRow : D (B := B) (Γ := Γ) (consGraph rows (singletonRow x w y) z)) :
    D (B := B) (Γ := Γ) (unary insertedTargets (suc ys) (rawCons (singletonRow x w y) z)) := by
  let row := singletonRow x w y
  have parsed := actualRawConsParser row z z rows exact_OriginalSparseParserNil oneRow
  obtain ⟨both⟩ := exactOpenTriple B α Γ 4 row y x w
  have equation : Derivation B Γ (equal row (tripleTerm 4 y x w)) := by
    rw [equalEqn]
    exact refl row
  have seen : Derivation B Γ (reports 4 row y x w) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft both) equation
  have tag : D (B := B) (Γ := Γ) (unary (guardAt 4) (suc z) row) :=
    ⟨Derivation.conjunctionLeft seen⟩
  have found : D (B := B) (Γ := Γ) (unary (field 0) y row) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight seen)⟩
  have step := exact_OpenTargetProjectionStepIntro B α Γ row y z ys tag found new
  have base := exact_OpenTargetProjectionNil B α Γ
  have all : D (B := B) (Γ := Γ) (unary scratchTargets (suc ys) rows) :=
    consValue targetBase targetStep rows row z (suc z) (suc ys) Fin.elim0 oneRow base step
  exact exact_OpenRawTargetProjectionIntro B α Γ _ rows ys parsed all

/-- The actual odd replacement certificate for a scalar step is a tag-5
node with empty kept list, the one removed scalar, and the one actual
carrying insertion row. All scratch terms are paired by the literal
codec and all original checker reports are constructed. -/
theorem exact_OriginalSingletonOddFromReports (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x w y xs ys rows : OTerm α)
    (oneSource : D (B := sourceBody (literalData i r) c) (Γ := Γ) (consGraph xs x z))
    (oneTarget : D (B := sourceBody (literalData i r) c) (Γ := Γ) (consGraph ys y z))
    (oneRow : D (B := sourceBody (literalData i r) c) (Γ := Γ) (consGraph rows (singletonRow x w y) z))
    (typedX : D (B := sourceBody (literalData i r) c) (Γ := Γ) (unary i (suc z) x))
    (typedY : D (B := sourceBody (literalData i r) c) (Γ := Γ) (unary i (suc z) y))
    (edge : D (B := sourceBody (literalData i r) c) (Γ := Γ) (programGraph r (suc z) ![x,w,y])) :
    D (B := sourceBody (literalData i r) c) (Γ := Γ)
      (certificate (literalData i r) true c (singletonCode x) (singletonCode y) (singletonWitness x w y)) := by
  let S := literalData i r
  let B := sourceBody S c
  let row := singletonRow x w y
  let ins := rawCons row z
  have src := actualRawConsParser x z z xs exact_OriginalSparseParserNil oneSource
  have dst := actualRawConsParser y z z ys exact_OriginalSparseParserNil oneTarget
  have parsed := actualRawConsParser row z z rows exact_OriginalSparseParserNil oneRow
  have carrierX := exact_IntroTypedScratchCons i B α Γ xs x z oneSource typedX
    (exact_TypedScratchNil i B α Γ)
  have carrierY := exact_IntroTypedScratchCons i B α Γ ys y z oneTarget typedY
    (exact_TypedScratchNil i B α Γ)
  have selected := exact_OriginalInsertedRowIntro r (singletonCode x) xs y x w src
    (headMember xs x z x oneSource ⟨refl x⟩) edge
  have scan := exact_OriginalRawScanIntro r ins (singletonCode x) rows parsed
    (exact_OriginalScanConsIntro r rows row z (singletonCode x) oneRow selected
      (exactOpenScanNil r B α Γ (singletonCode x)))
  have p : OriginalChangedSide i r c Γ (singletonCode x) (singletonCode y) z (singletonCode x)
      ins xs ys z xs ys xs ys x z :=
    ⟨⟨⟨src,dst,src⟩,carrierX,carrierY,oneSource⟩,exact_OriginalSparseParserNil,
      singletonProjection x w y rows ys oneTarget oneRow,leftNil xs,leftNil ys,
      exact_LiteralObserverReflexivity B α Γ xs,exact_LiteralObserverReflexivity B α Γ ys,scan⟩
  exact exact_LiteralChangedSideCertificate i r c (singletonCode x) (singletonCode y) z
    (singletonCode x) ins xs ys z xs ys xs ys x z p

#print axioms exact_OriginalSingletonOddFromReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepAssembleProof
