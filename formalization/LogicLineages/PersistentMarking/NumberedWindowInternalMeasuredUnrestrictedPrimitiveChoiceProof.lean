module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedPrimitiveChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureStepChecks (exact_CombineProgram exact_PhysicalAuxMeasure)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalFactoredCoverNumericProof (calibration selected)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalAuxExchangeMemoStepChecks (exact_PhysicalAuxMemoExchange)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepPrograms (exact_WindowPrimitiveLeaves)
open NumberedWindowInternalAuxWindowStepChecks (exact_PhysicalAuxWindow)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
  (measuredFactoredExchange exact_LiteralMeasuredFactoredCalibration)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_PhysicalLeastInstalledTuple)

/-- Genuine original, unrestricted physical measure, cover, exchange, and
intrinsic window. This is before adding the original own-cover wrapper. -/
theorem exact_OriginalMeasuredUnrestrictedPrimitiveChoice :
    ∃ (V baseM : Program 1) (P : Program 2) (G : Program 3),
      ActualRawSyntax V ∧ TermMeasureCalibrated (selectedMeasure (measureUpdate baseM P)) ∧
      ActualSelectedCoverOutput (factoredCover V (selectedMeasure (measureUpdate baseM P)) G) ∧
      ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
        HeadPairsSymmetric s.equivalentHeads →
        ∃ (base primitiveW : Program 2) (T : Program 1) (root other : Program 3),
          ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
          ActualTermExchange s base ∧
          ActualTermExchange s (measuredFactoredExchange s base V baseM P G) ∧
          ActualPackedWindow s (intrinsicQuery (selectedIntrinsic (windowUpdate primitiveW T))) := by
  obtain ⟨V,baseM,G,valid,baseMeasure,grammar,_⟩ := selected
  obtain ⟨P,combine⟩ := exact_CombineProgram
  have measure := exact_PhysicalAuxMeasure baseM P baseMeasure combine
  have cover := calibration V (selectedMeasure (measureUpdate baseM P)) G valid measure grammar
  refine ⟨V,baseM,P,G,valid,measure,cover,?_⟩
  intro entries s W hW symmetric
  obtain ⟨_,_,choose⟩ := exact_PhysicalLeastInstalledTuple
  obtain ⟨_,_,_,_,_,base,_,_,_,root,other,_,_,hroot,hother,_,_,hbase,_⟩ :=
    choose entries s W hW
  obtain ⟨primitiveW,T,fitW,fitT⟩ := exact_WindowPrimitiveLeaves s
  have directed := exact_PhysicalAuxMemoExchange s base V hbase valid
  have exchanged := exact_LiteralMeasuredFactoredCalibration s base V baseM P G symmetric cover measure directed
  have window := exact_PhysicalAuxWindow s primitiveW T fitW fitT
  exact ⟨base,primitiveW,T,root,other,hroot,hother,hbase,exchanged,window⟩

#print axioms exact_OriginalMeasuredUnrestrictedPrimitiveChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedPrimitiveChoiceProof
