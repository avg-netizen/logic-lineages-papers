module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr unionGraph CertifiedOriginSplit)
open NumberedWindowInternalDirectTypedUnionScratchTargets (CountMembershipForward)

abbrev literalData (i : Program 1) (r : Program 3) : Data :=
  data i (jRaw i) r (dCore i r permutation)

/-- Existing literal nested union conclusion at this exact body; splitting
actual certificates by origin remains an explicit proof premise. -/
def LiteralJUnion (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  let S := literalData i r
  CertifiedOriginSplit S c permutation →
  ∀ (α : Type) (Γ : List (Formula α)) (a b u : OTerm α),
    Pr S c Γ (membership true a) → Pr S c Γ (membership true b) →
    Pr S c Γ (unionGraph permutation a b u) → Pr S c Γ (membership true u)

def ExactLiteralJUnionFromCountMembership : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat),
    CountMembershipForward (sourceBody (literalData i r) c) permutation → LiteralJUnion i r c

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
