module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.MalformedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm refl)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atBound (n : Nat) (raw depth upper : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess depth (suc upper))) := by
  obtain ⟨he⟩ := (OriginalEnumerationDepth.ValueProof.internalMalformed n body alpha Delta raw depth hg).mp hd
  exact InternalOriginalPairingOrderArithmeticProof.strictTransport depth (suc upper) z (suc upper)
    ⟨he⟩ ⟨refl _⟩ ⟨InternalQuotientComparisonProof.zeroLessSuccessor upper⟩

theorem termBound (n : Nat) (raw depth size : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (OriginalTypedEnumerationDepthBound.termBound depth size)) :=
  atBound n raw depth (twice size) hg hd

theorem argumentsBound (n : Nat) (raw depth size : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (OriginalTypedEnumerationDepthBound.argumentsBound depth size)) :=
  atBound n raw depth (suc (twice size)) hg hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.MalformedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.MalformedProof
