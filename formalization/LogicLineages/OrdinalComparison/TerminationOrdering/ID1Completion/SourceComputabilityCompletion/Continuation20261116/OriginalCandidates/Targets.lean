module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Existing original Q specification, not a newly invented value function.
All raw inputs and original decode/default-zero branches remain quantified.
Native calibration alone uses the existing explicit head-signature calibration. -/
def NativeOriginal : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  ∀ v : List.Vector Nat 2,
    evaluate (candidates n arity H) v = Continuation20261114.SeededPrimaryPool.candidatesValue n arity v
/-- Actual Gamma and actual original packedCheck result are internally observed.
Nonzero means the literal retain branch, including for arbitrary H; no native
validity or Boolean-reflection hypothesis is hidden in this formula. -/
def retained {alpha : Type} (H : Program 1) (seed param candidate : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph2 OriginalClassCodes.gamma (.var (.inr (0 : Fin 2))) (seed.relabel Sum.inl) (param.relabel Sum.inl) ⊓
     graph2 (OriginalTypedDecoder.packedCheck H) (.var (.inr (1 : Fin 2)))
       (candidate.relabel Sum.inl) (.var (.inr 0)) ⊓
     (eqn (.var (.inr (1 : Fin 2))) (numeral 0)).not)
/-- Unrestricted actual candidates/Q membership. The sole premise is its output
graph. ClassCodes meaning supplies original typed seed admission, actual bounds,
sourceHeads, exact2*size fuel and root pairing, without a semantic supplier.
The new conjunct is precisely the original typed-only candidate retain test. -/
def InternalMembership : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param out candidate : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) ↔
   Nonempty (Derivation body Delta
     (OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓ retained H seed param candidate)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Targets
