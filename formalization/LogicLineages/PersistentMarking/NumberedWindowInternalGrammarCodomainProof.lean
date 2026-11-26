module

public import LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypeMembershipProof (exact_FiniteProgramImageTransfer)
open NumberedWindowInternalGrammarCodomainTargets

theorem exact_OpenFiniteGrammarCodomain : ExactOpenFiniteGrammarCodomain := by
  intro s closed body α Γ dom cod
  let premise := literalMembership s.types (rawCons dom cod)
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := premise :: Γ) dom cod
  obtain ⟨codomain⟩ := exact_FiniteProgramImageTransfer cellTail s.types s.types closed
    body α (premise :: Γ) (rawCons dom cod) cod
    ⟨Derivation.hypothesis List.mem_cons_self⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  exact ⟨Derivation.implicationIntroduction codomain⟩

theorem exact_FiniteGrammarCodomainInversion : ExactFiniteGrammarCodomainInversion := by
  intro s closed body α Γ dom cod member
  obtain ⟨rule⟩ := exact_OpenFiniteGrammarCodomain s closed body α Γ dom cod
  obtain ⟨member⟩ := member
  exact ⟨Derivation.implicationElimination rule member⟩

#print axioms exact_OpenFiniteGrammarCodomain
#print axioms exact_FiniteGrammarCodomainInversion

end LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainProof
