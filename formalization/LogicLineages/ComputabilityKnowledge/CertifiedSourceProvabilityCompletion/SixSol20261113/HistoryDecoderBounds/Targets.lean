module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- All source inputs, not only inputs known to be pair images. Derived from
actual bounded-scan range invariants; native calibration is not a premise. -/
def InternalRightDecoderBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,HistoryDecoder.decoder true⟩ → ∀ ctx (input : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (outputBound tag input))

/-- Every positive code has a tail code bounded by its predecessor, without
assuming that this code reconstructs as cons(head,tail). Needed for actual
course-of-values append reference coverage on arbitrary positive inputs. -/
def InternalPositiveTailBound : Prop := ∀ n (p : Program n) tag,
  (nodes p)[tag]? = some ⟨1,HistoryLookup.tail⟩ → ∀ ctx (input : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (HistoryBounds.weakBound (call tag (.succ input ::ᵥ nil)) input))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.Targets
