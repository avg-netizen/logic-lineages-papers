module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)

/-- The original output address of an application, accepted by the installed
scalar. From two accepted installed-scalar operand addresses with their
original reports at one context, the measured least `m` of the actual
auxiliary term is obtained under the genuine object continuation, and the
literal original address `addressTerm ctx cod m` built on that same witness
carries its original physical report and is accepted by the same installed
scalar. No window, least call, fixed-point law or address report at the output
is a premise. Besides the two retained syntax/refit type guards, the result
type guard of the scalar's own type checker `tv` at `cod` is explicit: scalar
acceptance of any address reporting result type `cod` entails it, and `tv` is
an arbitrary program. -/
def ExactInstalledApplicationOutputAddress : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv tv root other
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qf)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qa)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (leastGraph Q.source.cover Q.exchange Q.window s (ctx.relabel j) (cod.relabel j)
          ((auxiliaryTerm dom cod fn arg).relabel j) m)) →
      Nonempty (Derivation body Δ
        (addressReport (addressTerm (ctx.relabel j) (cod.relabel j) m)
          (ctx.relabel j) (cod.relabel j) m)) →
      Nonempty (Derivation body Δ
        (unary Q.scalar (suc z) (addressTerm (ctx.relabel j) (cod.relabel j) m))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- The same statement when the scalar's type checker is the syntax type guard
`TV` itself. The result type guard is then the second component of the
retained syntax guard, so only the two original type guards remain. -/
def ExactInstalledSyntaxGuardedApplicationOutputAddress : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv TV root other
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qf)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qa)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (leastGraph Q.source.cover Q.exchange Q.window s (ctx.relabel j) (cod.relabel j)
          ((auxiliaryTerm dom cod fn arg).relabel j) m)) →
      Nonempty (Derivation body Δ
        (addressReport (addressTerm (ctx.relabel j) (cod.relabel j) m)
          (ctx.relabel j) (cod.relabel j) m)) →
      Nonempty (Derivation body Δ
        (unary Q.scalar (suc z) (addressTerm (ctx.relabel j) (cod.relabel j) m))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets
