module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimum
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Least-hit minimality of the ACTUAL once-guarded initial representative,
on the original active domain. Both transparent target acceptance and the
original window/source activation are retained. The conclusion concerns the
same rank-observed class predicate used by the minimum, at the unchanged
seed and runtime parameter. No native calibration or class-coherence premise
is used to obtain this independent internal derivation. -/
def MinimumLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P
  let q := OriginalActiveObservedClass.inputs p H G W P
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out seed parameter earlier : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 T InternalOriginalStepGuard.one seed parameter ⊓
      (graph2 (OriginalActiveObservedClass.activation p H G W)
        InternalOriginalStepGuard.one seed parameter ⊓
        graph2 q.base.oldRepresentative out seed parameter)).imp
      (OriginalTransparentMinimum.atMost out seed ⊓
        (OriginalTransparentMinimum.graph3
          (OriginalTransparentMinimum.reflexiveClassTest T Q)
          InternalOriginalStepGuard.one seed out parameter ⊓
          ((InternalLessThan.strictLess earlier out).imp
            (OriginalTransparentMinimum.graph3
              (OriginalTransparentMinimum.reflexiveClassTest T Q)
              InternalOriginalStepGuard.one seed earlier parameter).not)))))

/-- One original tuple and one original class compiler are selected before
all windows and runtime contexts. The complete transparent-minimum Properties
(including the previous Package) use the active rank-observed class Q. The
unconditional final traversal/fold/Object rank laws use precisely its initial
minimum tuple s, followed by the same single guard, transparent decoder and
single variable refinement. No separate final tuple is selected. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) : Prop :=
  let Q := OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P
  let s := OriginalTransparentMinimum.minimumInputs H G Q p
  OriginalTransparentMinimum.ClassTestCalibrated n arity P ∧
  OriginalTransparentMinimum.Properties n arity p H G W Q ∧
  OriginalActiveObservedClass.HitLaw p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P ∧
  OriginalActiveObservedClass.GuardCollapseLaw p H G W P ∧
  MinimumLaw p H G W P ∧
  OriginalFinalGuardedRank.Properties n arity s H G W

/- These contracts do not assert structural class coherence, canonical
cancellation, an erasure certificate transformer, internal I/C or the original
closed all-term accessibility Derivation. Those obligations remain separate. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimum
