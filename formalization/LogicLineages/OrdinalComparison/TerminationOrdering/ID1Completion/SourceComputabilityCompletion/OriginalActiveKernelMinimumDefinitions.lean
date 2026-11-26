module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimum
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The checked active observed minimum, with the explicit calibrated kernel
as its class predicate. The original p remains the kernel's key supplier;
there is exactly one minimum construction and one original rank guard. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalActiveObservedClass.inputs p H G W
    (OriginalActiveClassKernel.classTest p H G W P)

/-- Two actual outputs of the SAME guarded minimum agree whenever their
original active typed seeds satisfy the actual rank-observed class relation.
The second seed's domain is a derived fact, not an added premise. No native
calibration, supplied row coherence or assumed representative equality occurs. -/
def CoherenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let R := (inputs p H G W P).base.oldRepresentative
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed other out otherOut parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
      (OriginalActiveClassKernel.Accepted p H G W
          OriginalRawSyntaxTransport.variableRankPackedRaw P seed other parameter ⊓
        (graph2 R out seed parameter ⊓ graph2 R otherOut other parameter))).imp
      (equal out otherOut)))

/-- Every actual active minimum output is a fixed point of that SAME
guarded representative at the SAME parameter. Its target/source/window
acceptance and the second computation are established internally. -/
def IdempotenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let R := (inputs p H G W P).base.oldRepresentative
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
      graph2 R out seed parameter).imp (graph2 R out out parameter)))

/-- Retain the entire previous active-minimum package, its original
calibrations and final rank laws at the literal kernel-minimum tuple. One
original p and one old class compiler P are chosen before all runtime windows
and contexts; the original pre-minimum key is never selected recursively. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  OriginalTransparentMinimum.ClassTestCalibrated n arity P ∧
    (OriginalActiveObservedMinimum.Properties n arity p H G W
        (OriginalActiveClassKernel.classTest p H G W P) ∧
      (OriginalActiveClassKernel.CharacterizationLaw p H G W
          OriginalRawSyntaxTransport.variableRankPackedRaw P ∧
        (OriginalActiveClassKernel.HitDomainLaw p H G W
            OriginalRawSyntaxTransport.variableRankPackedRaw P ∧
          (OriginalActiveClassKernel.RowCoherenceLaw p H G W
              OriginalRawSyntaxTransport.variableRankPackedRaw P ∧
            (CoherenceLaw p H G W P ∧ IdempotenceLaw p H G W P)))))

/- These laws give coherence and idempotence of the actual initial minimum
on its original active domain. They do not supply transport of the original
class key through context operations, final canonical cancellation, a general
certificate transformer, internal substitution/I/C or closed accessibility. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimum
