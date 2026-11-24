module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedOriginSplitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSpecializedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr unionGraph)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalLiteralCertifiedOriginSplitProof (exact_LiteralCertifiedOriginSplit)
open NumberedWindowInternalLiteralSingletonProgressSpecializedProof
  (exact_LiteralScalarSingletonImplication exact_LiteralParsedScalarMembersJ)
open NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof (exact_LiteralConditionalJUnion)

/-- The held original union of two J members is a J member in the
literal installed body, with no caller-supplied origin splitting. -/
theorem exact_LiteralJUnion (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (a b u : OTerm α)
    (left : Pr (literalData i r) c Γ (membership true a))
    (right : Pr (literalData i r) c Γ (membership true b))
    (join : Pr (literalData i r) c Γ (unionGraph permutation a b u)) :
    Pr (literalData i r) c Γ (membership true u) :=
  exact_LiteralConditionalJUnion i r c (exact_LiteralCertifiedOriginSplit i r c) α Γ a b u left right join

theorem exact_LiteralIToSingletonJ (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    Pr (literalData i r) c Γ ((membership false q).imp (singletonJ q)) :=
  exact_LiteralScalarSingletonImplication i r c (exact_LiteralCertifiedOriginSplit i r c) α Γ q

/-- All existing actual scalar I instances on the genuine members of
any positively parsed, typed original raw tape give actual J of that
tape. This is not a proof that all scalar terms are in I. -/
theorem exact_LiteralParsedJ (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw scratch : OTerm α)
    (parsed : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![raw])
    (typed : Pr (literalData i r) c Γ (typedAt i scratch))
    (members : Pr (literalData i r) c Γ (scalarMembers scratch)) :
    Pr (literalData i r) c Γ (membership true raw) :=
  exact_LiteralParsedScalarMembersJ i r c (exact_LiteralCertifiedOriginSplit i r c) α Γ raw scratch
    parsed typed members

#print axioms exact_LiteralJUnion
#print axioms exact_LiteralIToSingletonJ
#print axioms exact_LiteralParsedJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
