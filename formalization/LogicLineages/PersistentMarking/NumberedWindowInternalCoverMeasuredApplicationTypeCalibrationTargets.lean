module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets (ArrowCodomainInversion)

/-- The scalar type checker of the refitted installation: the syntax type
program `TV` and the window's refit guard `refitGuard s T`, both, on the same
input. It is a different program from `TV`; an installation using it accepts
an address only if its reported type also passes the refit guard. -/
def refittedScalarType (s : Settings) (TV T : Program 1) : Program 1 :=
  conjunction TV (refitGuard s T)

/-- Codomain inversion of physical membership in the literal grammar type
list of `s`, as a rule of the calculus over `body`: membership of
`rawCons dom cod` yields membership of `cod`. Its numeric shadow is closure of
the finite list `s.types` under arrow codomains; this definition is the
internal rule, not that numeric fact, and no implication from the numeric fact
to this rule is claimed. -/
def GrammarCodomainInversion (body : Positive (Fin 1)) (s : Settings) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
    Nonempty (Derivation body Γ
      (memberGraph (numeral (Encodable.encode s.types)) (rawCons dom cod))) →
    Nonempty (Derivation body Γ (memberGraph (numeral (Encodable.encode s.types)) cod))

/-- Codomain inversion of the refit guard follows from codomain inversion of
its two conjuncts: the supplied `T` and literal grammar-type membership. -/
def ExactRefitGuardCodomainInversionFromComponents : Prop :=
  ∀ (body : Positive (Fin 1)) (s : Settings) (T : Program 1),
    ArrowCodomainInversion body T → GrammarCodomainInversion body s →
    ArrowCodomainInversion body (refitGuard s T)

/-- All three type facts the general application statements require, derived
for the installation whose scalar type checker is `refittedScalarType s TV T`.
Two accepted operand addresses with matching function/argument reports at one
context yield, under codomain inversion of `TV` and of `refitGuard s T` and
nothing else about the type programs, the syntax guards at `dom` and `cod`,
the refit guards at `dom` and `cod`, and the scalar's own type checker at
`cod`. No rule from `TV` to the refit guard is a premise. -/
def ExactRefittedInstalledApplicationTypeGuards : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α),
    let Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other
    ArrowCodomainInversion body TV →
    ArrowCodomainInversion body (refitGuard s T) →
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qf)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qa)) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) ∧
    Nonempty (Derivation body Γ
      (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) ∧
    Nonempty (Derivation body Γ (unary (refittedScalarType s TV T) (suc z) cod))

/-- The accepted output address of an application for the refitted
installation, with no type-guard hypothesis: under codomain inversion of `TV`
and of `refitGuard s T`, two accepted installed-scalar operand addresses with
their original reports at one context yield, under the genuine object
continuation, the measured least `m` of the actual auxiliary term, the
original report of `addressTerm ctx cod m`, and its acceptance by the same
installed scalar. -/
def ExactRefittedInstalledApplicationOutputAddress : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other
    ArrowCodomainInversion body TV →
    ArrowCodomainInversion body (refitGuard s T) →
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

/-- Frontend acceptance for the refitted installation, with no type-guard
hypothesis: the same premises, and the continuation additionally receives the
unit graph of the actual installed application program on
`(qf, qa, addressTerm ctx cod m)`. -/
def ExactRefittedInstalledApplicationFrontendAcceptance : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other
    ArrowCodomainInversion body TV →
    ArrowCodomainInversion body (refitGuard s T) →
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

/-- Output functionality for the refitted installation, with no type-guard
hypothesis: the same premises, and the continuation additionally receives, for
every term `y` of the extended context, the internal implication from
acceptance of `(qf, qa, y)` by the installed application program to
`y = addressTerm ctx cod m`. -/
def ExactRefittedInstalledApplicationOutputFunctionalityContinuation : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α) (goal : Formula α),
    let Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other
    ArrowCodomainInversion body TV →
    ArrowCodomainInversion body (refitGuard s T) →
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

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets
