module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
/-- Actual original candidate/structural suppliers; keep the concrete seed pool,
actual length count, concrete D and full retained package at this NEW tuple. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (Q : Program 2) (B : Program 3),
    (∀ v, evaluate Q v = SeededPrimaryPool.candidatesValue n arity v) ∧
    (∀ v, evaluate B v = structuralValue n arity v) ∧
    let T := OriginalTypedDecoder.target H G
    let P := SeededPrimaryPool.pool T Q
    let E := edge B
    let L := SeededPrimaryPool.primary T Q E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P E ∧
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v = evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W
/-- Exact object-language factorization of the actual original type guard. -/
def InternalFactor : Prop := ∀ (B : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (source target parameter a b : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left a source)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left b target)) →
  (Nonempty (Derivation body Delta (graph3 (edge B) (numeral 1) source target parameter)) ↔
   Nonempty (Derivation body Delta (eqn a b ⊓ graph3 B (numeral 1) source target parameter)))
/-- Mismatched actual numeric type fields internally reject this edge. -/
def InternalMismatch : Prop := ∀ (B : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (source target parameter a b : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left a source)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left b target)) →
  Nonempty (Derivation body Delta (eqn a b).not) →
  Nonempty (Derivation body Delta (graph3 (edge B) (numeral 1) source target parameter).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
