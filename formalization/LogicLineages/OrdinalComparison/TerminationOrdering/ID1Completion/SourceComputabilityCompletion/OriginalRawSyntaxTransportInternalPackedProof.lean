module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- All selector outputs are obtained from the SAME supplied packed pair. -/
theorem shiftPackedComponents (packed tau raw transformed k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftRaw transformed k raw))) :
    Nonempty (Derivation body Delta (graph2 (leftOf (.projection 1)) tau k packed)) ∧
    Nonempty (Derivation body Delta (graph2
      (.composition shiftRaw ![.projection 0,rightOf (.projection 1)]) transformed k packed)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons k (Fin.cons packed Fin.elim0)
  have hl := unaryValue InternalUnpair.left (.projection 1) tau packed xs
    (pairLeft packed tau raw hp) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) raw packed xs
    (pairRight packed tau raw hp) (projectionValue 1 xs)
  exact ⟨hl,binaryValue shiftRaw (.projection 0) (rightOf (.projection 1))
    transformed k raw xs ht (projectionValue 0 xs) hr⟩

/-- The original three-input erasure wrapper copies only the outer type. -/
theorem erasePackedComponents (packed tau raw transformed d k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph3 eraseRaw transformed d k raw))) :
    Nonempty (Derivation body Delta (graph3 (leftOf (.projection 2)) tau d k packed)) ∧
    Nonempty (Derivation body Delta (graph3
      (.composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)])
      transformed d k packed)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons packed Fin.elim0))
  have hl := unaryValue InternalUnpair.left (.projection 2) tau packed xs
    (pairLeft packed tau raw hp) (projectionValue 2 xs)
  have hr := unaryValue InternalUnpair.right (.projection 2) raw packed xs
    (pairRight packed tau raw hp) (projectionValue 2 xs)
  refine ⟨hl,compositionValue eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)]
    transformed xs (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) ht ?_⟩
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases hr (fun q => Fin.elim0 q))) i

theorem shiftPackedForward (packed out tau raw transformed k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftRaw transformed k raw)))
    (ho : Nonempty (Derivation body Delta (graph2 shiftPackedRaw out k packed))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out tau transformed)) := by
  have hs := shiftPackedComponents packed tau raw transformed k hp ht
  exact binaryRecover InternalPairing.pairing (leftOf (.projection 1))
    (.composition shiftRaw ![.projection 0,rightOf (.projection 1)]) out tau transformed
    (Fin.cons k (Fin.cons packed Fin.elim0)) ho hs.1 hs.2

theorem shiftPackedBackward (packed out tau raw transformed k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftRaw transformed k raw)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out tau transformed))) :
    Nonempty (Derivation body Delta (graph2 shiftPackedRaw out k packed)) := by
  have hs := shiftPackedComponents packed tau raw transformed k hp ht
  exact binaryValue InternalPairing.pairing (leftOf (.projection 1))
    (.composition shiftRaw ![.projection 0,rightOf (.projection 1)]) out tau transformed
    (Fin.cons k (Fin.cons packed Fin.elim0)) ho hs.1 hs.2

theorem erasePackedForward (packed out tau raw transformed d k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph3 eraseRaw transformed d k raw)))
    (ho : Nonempty (Derivation body Delta (graph3 erasePackedRaw out d k packed))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out tau transformed)) := by
  have hs := erasePackedComponents packed tau raw transformed d k hp ht
  exact binaryRecover InternalPairing.pairing (leftOf (.projection 2))
    (.composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)]) out tau transformed
    (Fin.cons d (Fin.cons k (Fin.cons packed Fin.elim0))) ho hs.1 hs.2

theorem erasePackedBackward (packed out tau raw transformed d k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph3 eraseRaw transformed d k raw)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out tau transformed))) :
    Nonempty (Derivation body Delta (graph3 erasePackedRaw out d k packed)) := by
  have hs := erasePackedComponents packed tau raw transformed d k hp ht
  exact binaryValue InternalPairing.pairing (leftOf (.projection 2))
    (.composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)]) out tau transformed
    (Fin.cons d (Fin.cons k (Fin.cons packed Fin.elim0))) ho hs.1 hs.2

/-- Literal packed outer-type preservation, derived from original arithmetic
pair inverse laws and graph composition, with no Object or native premise. -/
theorem actualRawSyntaxInternalPacked : ActualRawSyntaxInternalPacked := by
  intro positive alpha Delta packed out tau raw transformed d k
  constructor
  · let A := graph2 InternalPairing.pairing packed tau raw ⊓ graph2 shiftRaw transformed k raw
    let B := graph2 shiftPackedRaw out k packed
    let C := graph2 InternalPairing.pairing out tau transformed
    have ha : Derivation positive (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
    have hf := shiftPackedForward packed out tau raw transformed k
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionLeft ha) B⟩
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionRight ha) B⟩
      (show Nonempty (Derivation positive (B :: A :: Delta) B) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hb := shiftPackedBackward packed out tau raw transformed k
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionLeft ha) C⟩
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionRight ha) C⟩
      (show Nonempty (Derivation positive (C :: A :: Delta) C) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hf⟩ := hf
    obtain ⟨hb⟩ := hb
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
  · let A := graph2 InternalPairing.pairing packed tau raw ⊓ graph3 eraseRaw transformed d k raw
    let B := graph3 erasePackedRaw out d k packed
    let C := graph2 InternalPairing.pairing out tau transformed
    have ha : Derivation positive (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
    have hf := erasePackedForward packed out tau raw transformed d k
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionLeft ha) B⟩
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionRight ha) B⟩
      (show Nonempty (Derivation positive (B :: A :: Delta) B) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hb := erasePackedBackward packed out tau raw transformed d k
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionLeft ha) C⟩
      ⟨InternalBetaTotalityProof.addHyp (Derivation.conjunctionRight ha) C⟩
      (show Nonempty (Derivation positive (C :: A :: Delta) C) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hf⟩ := hf
    obtain ⟨hb⟩ := hb
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
