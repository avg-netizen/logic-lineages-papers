module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion
open Continuation20261114
/-- A fresh strongest installed tuple with Q fixed to the literal candidate AST.
All original calibration premises and retained conclusions remain unchanged. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  let Q := candidateProgram n arity H
  ∃ (R D : Program 2) (U : Fin 19 → Program 3) (V C : Program 3) (K : Program 1),
    (∀ v, evaluate Q v = SeededPrimaryPool.candidatesValue n arity v) ∧
    (∀ v, evaluate R v = ExchangeNumericSuppliers.rankValue n v) ∧
    (∀ v, evaluate D v = ExchangeNumericSuppliers.depsValue n v) ∧
    (∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v) ∧
    (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) ∧
    (∀ v, evaluate C v = InstalledExchangeRecursor.validValue n v) ∧
    (∀ v, evaluate K v = InstalledExchangeRecursor.windowValue n v) ∧
    let J := StructuralExchangeFields.layer U V
    (∀ v, evaluate J v = ExchangeNumericSuppliers.layerValue n arity v) ∧
    InstalledStructuralFields.Targets.LambdaAt U V ∧
    InstalledStructuralFields.Targets.ApplicationAt U V ∧
    let B := InstalledExchangeRecursor.structural R D J C K
    (∀ v, evaluate B v = TypedPrimaryEdge.structuralValue n arity v) ∧
    let T := OriginalTypedDecoder.target H G
    let P := SeededPrimaryPool.pool T Q
    let E := TypedPrimaryEdge.edge B
    let L := SeededPrimaryPool.primary T Q E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P E ∧
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v = evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W

/-- Actual admitted seeded pool membership. Q output is not an endpoint premise;
it must be internally queried and eliminated. H/G have no native calibration premise. -/
def InternalPoolMembership : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (candidateProgram n arity H)) out seed parameter)) →
  (Nonempty (Derivation body Delta
    (graph2 Membership.contains (numeral 1) out candidate)) ↔
   Nonempty (Derivation body Delta
    (eqn candidate seed ⊔
      (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
       OriginalCandidates.Targets.retained H seed parameter candidate))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.Targets
