module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedRenamingSupport NumberedPrimaryWeakening

theorem actualPackedTraceSupport : NumberedTraceSupportTargets.ActualPackedTraceSupport := by
  intro Symbol arity symbols S above Gamma P count q r h hp
  induction h with
  | equivalent he => exact (NumberedPrimarySupportProof.primarySupport he P).mp hp
  | raw q r hs => exact NumberedStepSupportProof.stepSupport hs P hp
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 hp)

theorem actualTypedTraceSupport : NumberedTraceSupportTargets.ActualTypedTraceSupport := by
  intro Symbol arity symbols S above Gamma P tau count q r h hp
  exact actualPackedTraceSupport Symbol arity symbols S above Gamma P count ⟨tau,q⟩ ⟨tau,r⟩
    ((NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma tau count q r).mpr h) hp

theorem actualTupleTraceSupport : NumberedTraceSupportTargets.ActualTupleTraceSupport := by
  intro Symbol arity symbols S above Gamma P types count base target h hp
  induction h with
  | equivalent he => exact (NumberedPrimarySupportProof.actualArgumentPrimarySupport Symbol arity symbols S Gamma P _ _ _ he).mp hp
  | raw hs => exact NumberedStepSupportProof.actualArgumentStepSupport Symbol arity symbols S above Gamma P _ _ _ hs hp
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 hp)

theorem actualPackedTraceImage : NumberedTraceSupportTargets.ActualPackedTraceImage := by
  intro Symbol arity symbols S above Gamma Delta rho count q r h
  have hs := actualPackedTraceSupport Symbol arity symbols S above Delta (rangePredicate rho) count (renamePacked rho q) r h
    (NumberedRenamingSupportSupportProof.renamedSupported q.2 Delta rho)
  obtain ⟨source,he⟩ := (NumberedRenamingSupportProof.actualTermSupportImage Symbol arity Gamma Delta rho r.1 r.2).mp hs
  refine ⟨⟨r.1,source⟩,?_⟩
  exact congrArg (fun t => (⟨r.1,t⟩ : Packed Symbol arity Delta)) he

theorem actualTypedTraceImage : NumberedTraceSupportTargets.ActualTypedTraceImage := by
  intro Symbol arity symbols S above Gamma Delta rho tau count q r h
  have hs := actualTypedTraceSupport Symbol arity symbols S above Delta (rangePredicate rho) tau count (NumberedRewriteSyntax.rename q rho) r h
    (NumberedRenamingSupportSupportProof.renamedSupported q Delta rho)
  exact (NumberedRenamingSupportProof.actualTermSupportImage Symbol arity Gamma Delta rho tau r).mp hs

theorem actualTupleTraceImage : NumberedTraceSupportTargets.ActualTupleTraceImage := by
  intro Symbol arity symbols S above Gamma Delta rho types count base target h
  have hs := actualTupleTraceSupport Symbol arity symbols S above Delta (rangePredicate rho) types count (renameArguments base rho) target h
    (NumberedRenamingSupportSupportProof.renamedArgumentsSupported base Delta rho)
  exact (NumberedRenamingSupportProof.actualArgumentSupportImage Symbol arity Gamma Delta rho types target).mp hs

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportProof
