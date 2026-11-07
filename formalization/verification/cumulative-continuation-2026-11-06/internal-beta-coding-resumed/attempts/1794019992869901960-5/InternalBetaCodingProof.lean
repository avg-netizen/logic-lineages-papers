module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalRelationalCRT InternalBoundedCollection InternalBetaCoding
open InternalBetaCodingAssemblyProof

/-- Full internal bounded coding for the original relation and beta formula.
All witness bounds, moduli and CRT codes are obtained inside the calculus. -/
theorem actualBoundedBetaCoding : InternalBetaCodingTargets.ActualBoundedBetaCoding := by
  intro body α n R
  let Gamma := [availableBelow R n]
  have ha : Derivation body Gamma (availableBelow R n) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨hc⟩ := InternalBoundedCollectionProof.actualBoundedCollection body α n R
  have hc : Nonempty (Derivation body Gamma (collection R n)) :=
    ⟨Derivation.implicationElimination (weakenClosed hc Gamma) ha⟩
  obtain ⟨h⟩ := codingOfCollection R n hc
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingProof
