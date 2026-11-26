module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleInductionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding ConfinedStructuralInterpretation ActualLimitSubstitution CompatibleInductionProof

theorem interpretationSubstitution : CompatibleTargets.InterpretationSubstitution := by
  intro Symbol inst arity I M hcompat Γ Δ τ q s hs P ρ η ha
  exact (substitutionPair M hcompat q.val q.property Δ s hs P ρ η ha).1

theorem scannerSubstitution : CompatibleTargets.ScannerSubstitution := by
  intro Symbol inst arity I M hcompat Γ Δ τ q s hs P ρ η sm tm ha hc types υ args h
  exact (substitutionPair M hcompat q.val q.property Δ s hs P ρ η ha).2 sm tm hc types υ args h

theorem fixedPointCompatible : CompatibleTargets.FixedPointCompatible := by
  intro Symbol inst arity I above dec
  exact ActualLimitApplicationSupportProof.limitCurrentTuple above

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleProof
