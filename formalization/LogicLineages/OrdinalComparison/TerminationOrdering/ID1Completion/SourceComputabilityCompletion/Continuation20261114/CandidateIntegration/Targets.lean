module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary

/-- The SAME explicit new initial tuple, with concrete D and still-opaque L.
Its whole original rank-guard package is retained, not a replacement interface. -/
def RetainedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W L : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  Membership.ListCalibrated n arity L →
  let T := OriginalTypedDecoder.target H G
  let D := TransparentCandidate.candidate T
  let q := Membership.inputs p H G L D
  (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v =
    evaluate p.base.oldRepresentative v) ∧
  GlobalSourcePackage.InputsCalibrated n arity q ∧
  OriginalRankGuardedRepresentative.Properties n arity q H G W

/-- Select only the genuine original L leaf. D is the concrete transparent AST;
no internal correctness of L or equality with an old chosen tuple is claimed. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ L : Program 2, Membership.ListCalibrated n arity L ∧
    let q := Membership.inputs p H G L
      (TransparentCandidate.candidate (OriginalTypedDecoder.target H G))
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W

/-- Actual target admission now supplies D's actual output internally.
The only remaining leaf output premise is the genuine original L graph. -/
def ClassFactor : Prop := ∀ (T L : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (seed input parameter list : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 L list seed parameter)) →
  (Nonempty (Derivation body Delta
      (graph3 (Membership.classTest T L (TransparentCandidate.candidate T))
        (numeral 1) seed input parameter)) ↔
   Nonempty (Derivation body Delta
      (graph2 T (numeral 1) input parameter ⊓
       graph2 Membership.contains (numeral 1) list input)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Targets
