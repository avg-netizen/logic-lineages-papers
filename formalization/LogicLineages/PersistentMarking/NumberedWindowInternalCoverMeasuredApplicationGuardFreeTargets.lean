module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets
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

/-- Codomain inversion of one type program at an arrow code, as a rule of the
calculus over `body`: acceptance of `rawCons dom cod` yields acceptance of
`cod`. This is a property of the supplied program; it is not derivable for an
arbitrary `Program 1`. -/
def ArrowCodomainInversion (body : Positive (Fin 1)) (TV : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
    Nonempty (Derivation body Γ (unary TV (suc z) (rawCons dom cod))) →
    Nonempty (Derivation body Γ (unary TV (suc z) cod))

/-- The syntax type program entails the refit guard, as a rule of the calculus
over `body`: every type accepted by `TV` is accepted by `refitGuard s T`, that
is by `T` and by the physical grammar-type membership of `s`. -/
def SyntaxGuardRefits (body : Positive (Fin 1)) (s : Settings) (TV T : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (ty : OTerm α),
    Nonempty (Derivation body Γ (unary TV (suc z) ty)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) ty))

/-- The named calibration premise on the two type programs of an installation
with scalar type checker `TV`. Its two hypotheses are exactly the two type
facts that installed-scalar acceptance of a function address at
`rawCons dom cod` and of an argument address at `dom` supply; its conclusion is
exactly the part of the two retained type-guard conjunctions that those facts
do not already contain: `TV` at `cod` and the refit guard at `dom` and `cod`.
It mentions no address, window, least call, scalar or application program. -/
def TypeGuardArrowCalibration (body : Positive (Fin 1)) (s : Settings) (TV T : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
    Nonempty (Derivation body Γ (unary TV (suc z) (rawCons dom cod))) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom)) →
    Nonempty (Derivation body Γ (unary TV (suc z) cod ⊓
      (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)))

/-- The two component laws are sufficient for the named premise. -/
def ExactTypeGuardArrowCalibrationFromComponents : Prop :=
  ∀ (body : Positive (Fin 1)) (s : Settings) (TV T : Program 1),
    ArrowCodomainInversion body TV → SyntaxGuardRefits body s TV T →
    TypeGuardArrowCalibration body s TV T

/-- The two retained type-guard conjunctions of the application statements,
derived. For the installation with scalar type checker `TV`, two accepted
installed-scalar operand addresses with matching function/argument reports at
one context yield both conjunctions under the named calibration premise. No
type-guard derivation is a premise. -/
def ExactInstalledApplicationTypeGuards : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α),
    let Q := install s V TV M M0 B T base cv TV root other
    TypeGuardArrowCalibration body s TV T →
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qf)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qa)) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) ∧
    Nonempty (Derivation body Γ
      (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod))

/-- The accepted output address of an application with no type-guard
hypothesis. For the installation with scalar type checker `TV`, under the
named calibration premise on `TV` and `T`, two accepted installed-scalar
operand addresses with their original reports at one context yield, under the
genuine object continuation, the measured least `m` of the actual auxiliary
term, the original report of `addressTerm ctx cod m`, and its acceptance by
the same installed scalar. -/
def ExactInstalledGuardFreeApplicationOutputAddress : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv TV root other
    TypeGuardArrowCalibration body s TV T →
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

/-- Frontend acceptance of an application with no type-guard hypothesis: the
same premises, and the continuation additionally receives the unit graph of the
actual installed application program on `(qf, qa, addressTerm ctx cod m)`. -/
def ExactInstalledGuardFreeApplicationFrontendAcceptance : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv TV root other
    TypeGuardArrowCalibration body s TV T →
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
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- Output functionality of an application with no type-guard hypothesis: the
same premises, and the continuation additionally receives, for every term `y`
of the extended context, the internal implication from acceptance of
`(qf, qa, y)` by the installed application program to
`y = addressTerm ctx cod m`. -/
def ExactInstalledGuardFreeApplicationOutputFunctionalityContinuation : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv TV root other
    TypeGuardArrowCalibration body s TV T →
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

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets
