module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountMembershipChecks (exact_OpenLiteralCountMembershipForward)
open NumberedWindowInternalCertifiedUnionInnerProgressProof (UnionCarrierSupply)
open NumberedWindowInternalDirectTypedUnionCarrierProof (exact_SelectedUnionCarrierSupply)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets
open NumberedWindowInternalDirectTypedUnionLiteralJProof (exact_LiteralJUnionFromCountMembership)

/-- No caller-supplied arithmetic or carrier law; this uses the actual
literal observer's independently established open membership transport. -/
theorem exact_LiteralUnionCarrierSupply (i : Program 1) (r : Program 3) (c : Nat) :
    UnionCarrierSupply (literalData i r) c permutation :=
  exact_SelectedUnionCarrierSupply i r permutation c
    (exact_OpenLiteralCountMembershipForward (sourceBody (literalData i r) c))

/-- Only original certified origin splitting remains an explicit input
at this exact newly installed body. No claim for the old opaque checker. -/
theorem exact_LiteralConditionalJUnion (i : Program 1) (r : Program 3) (c : Nat) : LiteralJUnion i r c :=
  exact_LiteralJUnionFromCountMembership i r c
    (exact_OpenLiteralCountMembershipForward (sourceBody (literalData i r) c))

#print axioms exact_LiteralUnionCarrierSupply
#print axioms exact_LiteralConditionalJUnion
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof
