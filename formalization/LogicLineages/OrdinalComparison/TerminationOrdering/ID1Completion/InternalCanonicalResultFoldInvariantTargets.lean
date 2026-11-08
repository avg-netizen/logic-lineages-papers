module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalCanonicalResultFoldInvariant
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full internal payload invariant, with every original packed input and
requested type quantified INSIDE the payload predicate. The strong-induction
step and both leaf/application cases must be proved, not supplied as fields,
hypotheses, semantic truth or successful child runs. -/
def ActualOriginalCanonicalFoldPayloadInvariant : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (α : Type) (Gamma : List (Formula α))
    (payload : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (atPayload old representative member payload))

/-- Original V(input)=1 and left(input)=typ imply an INTERNALLY quantified
actual certified-fold result, with output validity, same raw tag and T-fixed.
All original leaves and contexts vary. There is no calibration, canonical
input, source-to-member, N-fixed, H-acceptance or successful-run premise. -/
def ActualOriginalCanonicalFoldCertifiedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (α : Type) (Gamma : List (Formula α))
    (input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises old member input typ).imp
      (hasCertifiedOutput old representative member input typ)))

/-- A consumer supplying the ACTUAL N graph obtains H=1 and the same output
invariant. Identify its output with the internally produced one by original
Program functionality; do not infer success from a raw fold graph alone. -/
def ActualOriginalCanonicalFoldOutputConsumer : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (α : Type) (Gamma : List (Formula α))
    (out input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises old member input typ).imp
      ((foldGraph old representative member out input).imp
        (successfulOutput old representative member out input typ))))

/-- Requested-type member(typ)=1 is a SEPARATE graph premise. The arbitrary
original source leaves do not imply it, even when V(input)=1. The conclusion
uses the existing canonical typed AST and actual good-run acceptance. -/
def ActualOriginalCanonicalFoldTypedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (α : Type) (Gamma : List (Formula α))
    (out input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((sourcePremises old member input typ).imp
      ((graph1 member InternalOriginalStepGuard.one typ).imp
        ((foldGraph old representative member out input).imp
          (typedOutput old representative member out input typ)))))

/-- Relabel-safe elimination of the genuine internally bound output. The
continuation sees both actual fold/success graphs and all output invariants
in ONE witness formula. No chosen natural value or output is pre-supplied. -/
def ActualOriginalCanonicalFoldOutputContinuation : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (α : Type) (Gamma : List (Formula α))
    (input typ : OrdinaryArithmetic.Term α) (psi : Formula α),
  Nonempty (Derivation body Gamma (sourcePremises old member input typ)) →
  (∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OrdinaryArithmetic.Term β),
    (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
    Nonempty (Derivation body Delta
      (certifiedOutput old representative member out (input.relabel j) (typ.relabel j))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantTargets
