module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
/-- Select actual ORIGINAL candidate and edge suppliers. Preserve all-vector
pool/count/list calibration and the full package at this explicit NEW tuple. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (Q : Program 2) (E : Program 3),
    (∀ v, evaluate Q v = candidatesValue n arity v) ∧
    let T := OriginalTypedDecoder.target H G
    let P := pool T Q
    let L := primary T Q E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P E ∧
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v = evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W
/-- Discharge the previously explicit seed-in-pool premise structurally. -/
def InternalSeedInPool : Prop := ∀ (T Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (seed parameter code : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (pool T Q) code seed parameter)) →
  Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) code seed))
/-- Exact internal original vertices decomposition, preserving seed duplicates
and the literal candidate tail. This does not infer semantic completeness of Q. -/
def InternalPoolCharacterization : Prop := ∀ (T Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (seed parameter code tail candidate : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 Q tail seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (pool T Q) code seed parameter)) →
  (Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) code candidate)) ↔
   Nonempty (Derivation body Delta
    (eqn candidate seed ⊔ graph2 Membership.contains (numeral 1) tail candidate)))
/-- Every member of the actual admitted primary output is in its actual
selected pool, without a seed-membership or native-reflection premise. -/
def InternalPrimaryCarrier : Prop := ∀ (T Q : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter code out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (pool T Q) code seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (primary T Q E) out seed parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included out code))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Targets
