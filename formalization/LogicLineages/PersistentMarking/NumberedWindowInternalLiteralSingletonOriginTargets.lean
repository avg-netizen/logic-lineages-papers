module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (certificate edge)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)

/-- Consume the one actual shared source/target tuple and its actual
removed and target members. No report from a second arbitrary partition. -/
def ExactLiteralSingletonMemberEdgeFromShared : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
    (src dst kept removed inserted s t k d a p sk tp head removedKey key : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Reports permutation permutation r B Γ src dst kept removed inserted s t k d a p sk tp →
    Nonempty (Derivation B Γ (consGraph s head z)) →
    Nonempty (Derivation B Γ (memberGraph d removedKey)) →
    Nonempty (Derivation B Γ (memberGraph t key)) →
    Nonempty (Derivation B Γ (edge S false c head key))

/-- Genuine scalar strict descendant of an actual held target member, in
the very same installed selected source body and physical odd witness. -/
def ExactInstalledLiteralSingletonMemberEdge : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (head dst w decoded key : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S true c (singletonCode head) dst w)) →
    Nonempty (Derivation B Γ (unary parser (suc decoded) dst)) →
    Nonempty (Derivation B Γ (memberGraph decoded key)) →
    Nonempty (Derivation B Γ (edge S false c head key))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginTargets
