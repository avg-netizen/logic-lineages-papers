module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
/-- Actual P/E existence and all-vector original calibration, including
malformed/default inputs, at the SAME new tuple with concrete length∘P. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (P : Program 2) (E : Program 3),
    TransparentPrimary.SuppliersCalibrated n arity (countOfPool P) P E ∧
    let T := OriginalTypedDecoder.target H G
    let L := primary T P E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v =
      evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W
/-- Structural graph recovery from the concrete AST, never native reflection. -/
def InternalCountLength : Prop := ∀ (P : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (seed parameter pool size : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 P pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (countOfPool P) size seed parameter)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size pool))
/-- The actual admitted primary output is membership-stable under one more
literal expansion using the exact selected pool. No code equality claimed. -/
def InternalPrimaryStability : Prop := ∀ (T P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter pool out next : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 P pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (primary T P E) out seed parameter)) →
  Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out))
/-- Actual internal edge closure of the new selected L, explicitly requiring
candidate pool membership and actual E acceptance. No original E correctness
or selected-pool adequacy is hidden in this generic prerequisite. -/
def InternalEdgeClosure : Prop := ∀ (T P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter pool out source candidate : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 P pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (primary T P E) out seed parameter)) →
  Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out source)) →
  Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) pool candidate)) →
  Nonempty (Derivation body Delta (graph3 E (numeral 1) source candidate parameter)) →
  Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out candidate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Targets
