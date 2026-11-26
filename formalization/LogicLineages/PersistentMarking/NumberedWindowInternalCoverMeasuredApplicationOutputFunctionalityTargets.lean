module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)

/-- Output functionality of the installed application program, with the
measured least held through its graph. From the two original operand reports
at one context and a measured least `m` of the actual auxiliary term, every
`y` the installed application program accepts on `(qf, qa)` equals the literal
address `addressTerm ctx cod m`. No type guard, scalar acceptance, arrow
report, shell equation, block witness, uniqueness of reports or injectivity of
`addressTerm` is a premise. -/
def ExactInstalledApplicationOutputFunctionality : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg m y : OTerm α),
    let Q := install s V TV M M0 B T base cv tv root other
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ
      (leastGraph Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg) m)) →
    Nonempty (Derivation body Γ (programGraph Q.application (suc z) ![qf,qa,y])) →
    Nonempty (Derivation body Γ (eqn y (addressTerm ctx cod m)))

/-- The frontend-acceptance statement with functionality added. The premises
are exactly those of frontend acceptance. Under the genuine object
continuation the same fresh measured least `m` carries, besides the least
call, the report and scalar acceptance of `addressTerm ctx cod m` and the unit
application graph on it, the internal implication for every term `y` of the
extended context: acceptance of `(qf, qa, y)` by the installed application
program implies `y = addressTerm ctx cod m`. -/
def ExactInstalledApplicationOutputFunctionalityContinuation : Prop :=
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
      Nonempty (Derivation body Δ
        (programGraph Q.application (suc z)
          ![qf.relabel j,qa.relabel j,addressTerm (ctx.relabel j) (cod.relabel j) m])) →
      (∀ y : OTerm β, Nonempty (Derivation body Δ
        ((programGraph Q.application (suc z) ![qf.relabel j,qa.relabel j,y]).imp
          (eqn y (addressTerm (ctx.relabel j) (cod.relabel j) m))))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- The same statement when the scalar's type checker is the syntax type guard
`TV` itself: only the two original type guards remain beside the two accepted
operand addresses and their reports. -/
def ExactInstalledSyntaxGuardedApplicationOutputFunctionalityContinuation : Prop :=
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
      Nonempty (Derivation body Δ
        (programGraph Q.application (suc z)
          ![qf.relabel j,qa.relabel j,addressTerm (ctx.relabel j) (cod.relabel j) m])) →
      (∀ y : OTerm β, Nonempty (Derivation body Δ
        ((programGraph Q.application (suc z) ![qf.relabel j,qa.relabel j,y]).imp
          (eqn y (addressTerm (ctx.relabel j) (cod.relabel j) m))))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets
