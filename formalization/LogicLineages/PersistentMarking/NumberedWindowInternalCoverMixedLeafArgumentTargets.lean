module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafArgumentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafTypeTest)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider argumentExists)

def namedGrammarHead (s : Settings) (b : Bool) : Program 1 :=
  conjunction (header b.toNat 2) (leafTypeTest s)

def unionHeadGuard (X Y : Program 1) : Program 1 :=
  branch (normalize X) (normalize Y) (literal 1 1)

def mixedLeafHead (s : Settings) : Program 1 :=
  unionHeadGuard (typeOnlyHeadGuard s) (unionHeadGuard (namedGrammarHead s false) (namedGrammarHead s true))

def OriginalMixedLeaf (s : Settings) (raw : Nat) : Prop :=
  (∃ ty, unpackNode raw = some (3,[ty]) ∧ ty ∈ s.types) ∨
  (∃ (b : Bool) (ty i : Nat), unpackNode raw = some (b.toNat,[ty,i]) ∧ ty ∈ s.types)

def ExactCoverMixedLeafHeadNumeric : Prop :=
  ∀ (s : Settings) (raw : Nat), run (mixedLeafHead s) raw = 1 ↔ OriginalMixedLeaf s raw

def ExactOpenCoverNamedGrammarHead : Prop :=
  ∀ (s : Settings) (b : Bool) (M : Program 1) (body : Positive (Fin 1)),
    HeadProvider (namedSharedMeasure M) (namedGrammarHead s b) s body

def ExactOpenCoverMixedLeafHeadProvider : Prop :=
  ∀ (s : Settings) (M : Program 1) (body : Positive (Fin 1)),
    HeadProvider (namedSharedMeasure M) (mixedLeafHead s) s body

def ExactOpenCoverMixedLeafArgumentList : Prop :=
  ∀ (s : Settings) (M : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (raw : OTerm α),
    Nonempty (Derivation body Γ (unary (argumentReject (mixedLeafHead s)) z raw)) →
    Nonempty (Derivation body Γ (argumentExists (namedSharedMeasure M) s raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafArgumentTargets
