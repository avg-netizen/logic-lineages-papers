module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Native calibration alone uses the existing head-signature calibration.
All raw seed/parameter inputs, including every original failure/default, remain. -/
def NativeOriginal : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  ∀ v : List.Vector Nat 2, evaluate (classCodes n arity H) v = classCodesValue n arity v
/-- Nine INTERNAL witnesses: candidate raw, root type, types, encoded heads,
size, label, context length, actual doubled fuel, admission result. All selectors
are observed from the original seed/parameter, not supplied as semantic inputs.
Admission is nonzero because the actual branch tests zero, even for arbitrary H. -/
def meaning {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) : Formula alpha :=
  let s := seed.relabel Sum.inl
  let p := param.relabel Sum.inl
  let c := candidate.relabel Sum.inl
  let x : Fin 9 → OTerm (alpha ⊕ Fin 9) := fun i => .var (.inr i)
  InternalFiniteBlocks.block
    (graph2 rootType (x 1) s p ⊓
     graph2 types (x 2) s p ⊓
     graph2 (heads n arity) (x 3) s p ⊓
     graph2 (size n) (x 4) s p ⊓
     graph2 (labels n) (x 5) s p ⊓
     graph2 bound (x 6) s p ⊓
     graph2 (fuel n) (x 7) s p ⊓
     graph2 (admitted n H) (x 8) s p ⊓
     (eqn (x 8) (numeral 0)).not ⊓
     graph2 InternalPairing.pairing c (x 1) (x 0) ⊓
     OriginalEnumerationFields.Targets.accepted n (x 0) (x 6) (x 2) (x 3) (x 5) (x 4) ⊓
     OriginalEnumerationMembership.Targets.depthBound n (x 0) (x 7))
/-- Actual classCodes membership, with ONLY its actual output graph supplied.
No head calibration, code/seed validity, semantic bounds, correct enumeration,
encoded image, recursive membership or candidate-decoder correctness premise. -/
def InternalMembership : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param out candidate : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) ↔
   Nonempty (Derivation body Delta (meaning n arity H seed param candidate)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
