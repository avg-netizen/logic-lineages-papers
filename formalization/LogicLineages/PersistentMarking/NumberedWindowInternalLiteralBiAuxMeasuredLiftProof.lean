module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredParentsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverGuardedExchangeNumericProof (calibration)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredExchangeThinNumericProof (exact_LiteralMeasuredExchangeCalibration)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange exact_LiteralPairedCalibration)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets (accepted)
open NumberedWindowInternalMeasuredExchangeThinOpenCompareProof (compareCases)
open NumberedWindowInternalMeasuredExchangeThinOpenComposeProof (recoverChild)
open NumberedWindowInternalMeasuredExchangeThinOpenParentsProof (ParentReports renameReports renameUnary)
open NumberedWindowInternalLiteralBiAuxMeasuredParentsProof
open NumberedWindowInternalLiteralBiAuxRawMemoOpenProof (biAuxRawMemo)
open NumberedWindowInternalLiteralBiAuxRawMemoLiftProof
open NumberedWindowInternalLiteralBiAuxRawMemoCalibrationProof
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem varyAuxiliaryRename {β : Type} (v : Bool) (dom cod q fixed : OTerm α) (j : α → β) :
    (varyAuxiliary v dom cod q fixed).relabel j =
      varyAuxiliary v (dom.relabel j) (cod.relabel j) (q.relabel j) (fixed.relabel j) := by
  cases v
  · exact auxiliaryRename dom cod q fixed j
  · exact auxiliaryRename dom cod fixed q j

private theorem withFixed (s : Settings) (X : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (v : Bool) (dom cod q r fixed k : OTerm α)
    (held : ParentReports V (biAuxRawMemo X V) B Γ (varyAuxiliary v dom cod q fixed)
      (varyAuxiliary v dom cod r fixed))
    (left : D B Γ (unary (selectedMeasure (measureUpdate baseM P)) k q))
    (right : D B Γ (unary (selectedMeasure (measureUpdate baseM P)) k r)) :
    D B Γ (accepted (biAuxMeasuredExchange s X V baseM P G)
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let M := selectedMeasure (measureUpdate baseM P)
  apply programCases M ![fixed] _
  intro β j Δ f keep seen
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,varyAuxiliaryRename]
  rw [unaryInputsRename] at seen
  have moved := renameReports held j Δ keep
  simp only [varyAuxiliaryRename] at moved
  have l := renameUnary M k q j Δ keep left
  have r' := renameUnary M k r j Δ keep right
  let d := dom.relabel j
  let c := cod.relabel j
  let x := q.relabel j
  let y := r.relabel j
  let b := fixed.relabel j
  let m := k.relabel j
  cases v
  · exact exact_OpenMeasuredBiAuxParent s X V baseM P G d c x y b b m f moved l r' seen seen
  · exact exact_OpenMeasuredBiAuxParent s X V baseM P G d c b b x y f m moved seen seen l r'

theorem exact_OpenMeasuredBiAuxExchangeLifts (s : Settings) (X : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (v : Bool) (dom cod q r fixed : OTerm α)
    (child : D B Γ (accepted (biAuxMeasuredExchange s X V baseM P G) q r))
    (source : D B Γ (unary V (suc z) (varyAuxiliary v dom cod q fixed)))
    (target : D B Γ (unary V (suc z) (varyAuxiliary v dom cod r fixed))) :
    D B Γ (accepted (biAuxMeasuredExchange s X V baseM P G)
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let M := selectedMeasure (measureUpdate baseM P)
  let Raw := biAuxRawMemo X V
  let C := factoredCover V M G
  let a := varyAuxiliary v dom cod q fixed
  let b := varyAuxiliary v dom cod r fixed
  obtain ⟨f,bk,measures⟩ := recoverChild M Raw C s q r child
  have original := (exact_OpenPairedRawReports Raw q r).mpr ⟨f,bk⟩
  have moved := exact_OpenBiAuxRawExchangeLifts X V v dom cod q r fixed original source target
  obtain ⟨f',bk'⟩ := (exact_OpenPairedRawReports Raw a b).mp moved
  have physical : ParentReports V Raw B Γ a b := ⟨f',bk',source,target⟩
  apply compareCases M q r _ measures
  intro β j Δ mu keep first second
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,varyAuxiliaryRename]
  have parents := renameReports physical j Δ keep
  simp only [a,b,varyAuxiliaryRename] at parents
  exact withFixed s X V baseM P G v (dom.relabel j) (cod.relabel j)
    (q.relabel j) (r.relabel j) (fixed.relabel j) mu parents first second

theorem exact_LiteralMeasuredBiAuxExchange (s : Settings) (X : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (symmetry : HeadPairsSymmetric s.equivalentHeads)
    (raw : ActualTermExchange s X) (syntaxFit : TermSyntaxCalibrated V)
    (measureFit : TermMeasureCalibrated (selectedMeasure (measureUpdate baseM P)))
    (cover : ActualSelectedCoverOutput (factoredCover V (selectedMeasure (measureUpdate baseM P)) G)) :
    ActualTermExchange s (biAuxMeasuredExchange s X V baseM P G) := by
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  let Raw := biAuxRawMemo X V
  have exactRaw := exact_LiteralBiAuxRawMemo s X V raw syntaxFit
  have measured := exact_LiteralMeasuredExchangeCalibration s M Raw measureFit exactRaw
  have paired := exact_LiteralPairedCalibration s (measuredExchange M Raw) symmetry measured
  exact calibration C s (pairedExchange (measuredExchange M Raw)) cover paired

#print axioms varyAuxiliaryRename
#print axioms exact_OpenMeasuredBiAuxExchangeLifts
#print axioms exact_LiteralMeasuredBiAuxExchange
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredLiftProof
