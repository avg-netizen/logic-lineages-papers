module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (carrier certificate membership)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)

/-- Actual same observer [lhs,rhs]; no assumption of reversed observer tape. -/
def LiteralReverseMembership (B : Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (lhs rhs key : OTerm α),
    Nonempty (Derivation B Γ (observer permutation lhs rhs)) →
    Nonempty (Derivation B Γ (memberGraph rhs key)) →
    Nonempty (Derivation B Γ (memberGraph lhs key))

def ExactLiteralEmptyCertificateImpossible : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (dst w : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    LiteralReverseMembership B →
    Nonempty (Derivation B Γ (certificate S true c z dst w)) →
    Nonempty (Derivation B Γ (⊥ : Formula α))

def ExactLiteralEmptyJ : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α)),
    let S := literalData i r
    let B := sourceBody S c
    LiteralReverseMembership B →
    Nonempty (Derivation B Γ (membership true (z : OTerm α)))

def ExactLiteralScalarSingletonCarrier : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (q : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (membership false q)) →
    Nonempty (Derivation B Γ (carrier S true c (singletonCode q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
