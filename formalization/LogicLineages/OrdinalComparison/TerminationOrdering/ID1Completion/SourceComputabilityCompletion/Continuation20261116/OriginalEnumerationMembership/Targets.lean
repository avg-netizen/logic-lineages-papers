module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
/-- Actual original depth, existentially observed, bounded by original fuel.
Malformed depth0 behavior is preserved; this formula alone is NOT membership. -/
def depthBound {alpha : Type} (n : Nat) (raw fuel : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block
    (graph1 (OriginalEnumerationDepth.depth n) (.var (.inr (0 : Fin 1))) (raw.relabel Sum.inl) ⊓
      InternalLessThan.strictLess (.var (.inr 0)) (suc (fuel.relabel Sum.inl)))
/-- Finite-symbol specialization of original ActualCodeEnumeration, retaining
all original S/H/bounds/fuel/candidate quantifiers and actual compiler encodings.
This is not an assertion of an arbitrary-Symbol numeric codec. -/
def NativeOriginal : Prop := ∀ (n : Nat) (S : List Source.Ty)
    (H : List (NumberedAuxiliaryCoding.HeadCode (Fin n)))
    (labels tupleBound variableBound fuel : Nat) (c : NumberedAuxiliaryCoding.Code (Fin n)),
  (evaluate contains (List.Vector.ofFn ![
    evaluate (OriginalEnumerationRecursion.enumeration n) (List.Vector.ofFn ![
      Encodable.encode (variableBound,fuel),Encodable.encode (S,(H,(labels,tupleBound)))]),
    NumberedLeastCodeRepresentative.codeNumber c]) = 1 ↔
   NumberedAuxiliaryEnumeration.Fields S H labels tupleBound variableBound c ∧
     NumberedAuxiliaryEnumeration.depth c ≤ fuel)
/-- Full original membership/depth characterization, on every raw candidate and
parameter. Only actual total node/parameter pairing observations and the actual
enumeration output are premises. No assumed code guard, encoded-image restriction,
recursive membership oracle, successful cache answer, or native truth is supplied.
The depth witness is internal and the Fields program retains its original guard. -/
def InternalMembership : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node param p2 p3 out raw variableBound fuel types heads labels tupleBound : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalPairing.pairing node variableBound fuel)) →
  Nonempty (Derivation body Delta
    (graph2 InternalPairing.pairing param types p2)) →
  Nonempty (Derivation body Delta
    (graph2 InternalPairing.pairing p2 heads p3)) →
  Nonempty (Derivation body Delta
    (graph2 InternalPairing.pairing p3 labels tupleBound)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out raw)) ↔
   Nonempty (Derivation body Delta
    (OriginalEnumerationFields.Targets.accepted n raw variableBound types heads labels tupleBound ⊓
      depthBound n raw fuel)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
