module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary UniformCertificateCompletion

/-- Select actual subordinate suppliers, retain original calibration and the
complete prior Package/rank laws at exactly the NEW concrete L/D tuple. -/
def SelectedTuple : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∃ (C P : Program 2) (E : Program 3),
    TransparentPrimary.SuppliersCalibrated n arity C P E ∧
    let T := OriginalTypedDecoder.target H G
    let L := TransparentPrimary.primary T C P E
    let q := Membership.inputs p H G L (TransparentCandidate.candidate T)
    Membership.ListCalibrated n arity L ∧
    (∀ v : List.Vector Nat 2, evaluate q.base.oldRepresentative v =
      evaluate p.base.oldRepresentative v) ∧
    GlobalSourcePackage.InputsCalibrated n arity q ∧
    OriginalRankGuardedRepresentative.Properties n arity q H G W

/-- The artificial diagonal override is internally redundant on target-admitted
seeds. This is graph acceptance equivalence, not native reflection. -/
def WrapperAcceptance : Prop := ∀ (T C P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  (Nonempty (Derivation body Delta
    (graph3 (OriginalTransparentMinimum.reflexiveClassTest T (kernel T C P E))
      (numeral 1) seed candidate parameter)) ↔
   Nonempty (Derivation body Delta
    (graph3 (kernel T C P E) (numeral 1) seed candidate parameter)))

/-- Least hit of the actual original calibrated class, before rank fallback.
No postguard minimality is asserted. -/
def ActualMinimum : Prop := ∀ (T C P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out seed parameter earlier : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 T (numeral 1) seed parameter ⊓
      graph2 (OriginalTransparentMinimum.minimum T (kernel T C P E)) out seed parameter).imp
      (OriginalTransparentMinimum.atMost out seed ⊓
        (graph3 (kernel T C P E) (numeral 1) seed out parameter ⊓
          ((InternalLessThan.strictLess earlier out).imp
            (graph3 (kernel T C P E) (numeral 1) seed earlier parameter).not)))))

/-- SAME new initial tuple after the accepted rank guard: actual class
membership, not merely its reflexive override; no class coherence claim. -/
def GuardedActualClass : Prop := ∀ (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W C P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out seed parameter : OTerm alpha),
  let T := OriginalTypedDecoder.target H G
  let L := TransparentPrimary.primary T C P E
  let initial := Membership.inputs p H G L (TransparentCandidate.candidate T)
  let guarded := OriginalRankGuardedRepresentative.transparentInputs H G W initial
  Nonempty (Derivation body Delta
    ((graph2 T (numeral 1) seed parameter ⊓
      graph2 guarded.base.oldRepresentative out seed parameter).imp
      (graph3 (kernel T C P E) (numeral 1) seed out parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Targets
