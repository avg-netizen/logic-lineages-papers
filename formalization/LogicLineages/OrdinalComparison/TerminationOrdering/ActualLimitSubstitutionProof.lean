module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionInductionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding ConfinedStructuralInterpretation ActualLimitSubstitution ActualLimitSubstitutionInductionProof

theorem interpretationSubstitution : ActualLimitSubstitutionTargets.InterpretationSubstitution := by
  intro Symbol inst arity I above dec Γ Δ τ q s hs P ρ η ha
  exact (substitutionPair above q.val q.property Δ s hs P ρ η ha).1

theorem scannerSubstitution : ActualLimitSubstitutionTargets.ScannerSubstitution := by
  intro Symbol inst arity I above dec Γ Δ τ q s hs P ρ η sm tm ha hc types υ args h
  exact (substitutionPair above q.val q.property Δ s hs P ρ η ha).2 sm tm hc types υ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionProof
