module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenParentsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalAuxExchangeMemoThinLiftChecks (derive)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets
open NumberedWindowInternalMeasuredExchangeThinOpenCompareProof (compareCases)
open NumberedWindowInternalMeasuredExchangeThinOpenComposeProof (recoverChild)
open NumberedWindowInternalMeasuredExchangeThinOpenParentsProof (ParentReports renameReports fromCommonFunction)


theorem exact_OpenMeasuredFactoredAuxLift : ExactOpenMeasuredFactoredAuxLift := by
  intro s baseX V baseM P G body α Γ dom cod fn fn' arg X a b
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  let rawX := selected (step baseX V)
  let h := accepted X fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)
  let Δ := h :: Γ
  have facts : Derivation body Δ h := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward,backward,equalMeasures⟩ := recoverChild M rawX C s fn fn' ⟨Derivation.conjunctionLeft facts⟩
  let guards := Derivation.conjunctionRight facts
  let first := Nonempty.intro (Derivation.conjunctionLeft guards)
  let second := Nonempty.intro (Derivation.conjunctionRight guards)
  have parent : ParentReports V rawX body Δ a b :=
    ⟨derive baseX V dom cod fn fn' arg forward first second,
      derive baseX V dom cod fn' fn arg backward second first,first,second⟩
  have result : Nonempty (Derivation body Δ (accepted X a b)) := by
    refine compareCases M fn fn' (accepted X a b) equalMeasures ?_
    intro β j Θ m hJ childA childB
    simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,a,b,auxiliaryRename]
    have ready := renameReports parent j Θ hJ
    simp only [a,b,auxiliaryRename] at ready
    exact fromCommonFunction s baseX V baseM P G (dom.relabel j) (cod.relabel j)
      (fn.relabel j) (fn'.relabel j) (arg.relabel j) m ready childA childB
  obtain ⟨out⟩ := result
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenMeasuredFactoredAuxLift

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenChecks
