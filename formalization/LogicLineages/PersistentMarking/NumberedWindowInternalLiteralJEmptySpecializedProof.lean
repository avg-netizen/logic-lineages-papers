module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptySpecializedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralMemberReverse)
open NumberedWindowInternalLiteralJEmptyProof (exact_LiteralEmptyJ)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)

theorem exact_LiteralSelectedEmptyJ (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ (membership true (z : OTerm α))) := by
  apply exact_LiteralEmptyJ i r c α Γ
  intro β Δ lhs rhs key accepted present
  exact exact_LiteralMemberReverse (sourceBody (literalData i r) c) β Δ lhs rhs key accepted present

#print axioms exact_LiteralSelectedEmptyJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptySpecializedProof
