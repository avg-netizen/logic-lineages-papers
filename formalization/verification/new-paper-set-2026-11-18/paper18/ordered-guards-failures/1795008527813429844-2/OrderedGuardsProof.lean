module
public import LogicLineages.StandardControlCurrent.OrderedGuardsCalibrationProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.StatementChecks
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.StatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedGuardsProof
open OrdinalComparison PolynomialGraphCompletion FullWordGuardCompletion CanonicalGuardSelector

theorem domains : OrderedGuardsTargets.CompiledDomains := by
  intro D p hD hp x y hx hy
  have h := StatementChecks.fixed_compiledDomains D p hD hp x y hx hy
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  refine ⟨(wordCalibration D _ ha.1 x).1.mpr h.1,
    (wordCalibration D _ ha.2 y).1.mpr h.2.1,h.2.2.1,?_⟩
  intro q hq
  have hqa := (RunnerProof.admissionCorrect D q).mp
    ((StatementChecks.fixed_compiledSyntax D p hD hp).2.2.2.2.2 q hq)
  have hqd := h.2.2.2 q hq
  have hpa := (CanonicalGuardSelector.StatementChecks.fixed_viewSyntax D q.1 hqa.1).2.2.2.2.1
  have hpb := (CanonicalGuardSelector.StatementChecks.fixed_viewSyntax D q.2 hqa.2).2.2.2.2.1
  exact ⟨(wordCalibration D _ hqa.1 x).1.mpr hqd.1,
    (wordCalibration D _ hqa.2 y).1.mpr hqd.2.1,
    (wordCalibration D _ hpa x).1.mpr hqd.2.2.1,
    (wordCalibration D _ hpb y).1.mpr hqd.2.2.2⟩

theorem threeWay : OrderedGuardsTargets.CompiledThreeWay := by
  intro D p hD hp x y hx hy hyx
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  have hd := domains D p hD hp x y hx hy
  have hxv := (wordCalibration D _ ha.1 x).2 hd.1
  have hyv := (wordCalibration D _ ha.2 y).2 hd.2.1
  simpa only [hxv,hyv] using StatementChecks.fixed_compiledThreeWay D p hD hp x y hx hy hyx

theorem sameVariable : OrderedGuardsTargets.CompiledSameVariable := by
  intro D p hD hp x hx
  have ha := (RunnerProof.admissionCorrect D p).mp hp
  have hd := domains D p hD hp x x hx hx
  have hxv := (wordCalibration D _ ha.1 x).2 hd.1
  have hyv := (wordCalibration D _ ha.2 x).2 hd.2.1
  simpa only [hxv,hyv] using StatementChecks.fixed_compiledSameVariable D p hD hp x hx

theorem full : OrderedGuardsTargets.Full :=
  ⟨wordCalibration,StatementChecks.fixed_compilerCalibration,StatementChecks.fixed_compiledSyntax,
    domains,threeWay,sameVariable,StatementChecks.fixed_boundedCompilerPrograms,StatementChecks.fixed_compilerProgram⟩
end LogicLineages.StandardControlCurrent.OrderedGuardsProof
