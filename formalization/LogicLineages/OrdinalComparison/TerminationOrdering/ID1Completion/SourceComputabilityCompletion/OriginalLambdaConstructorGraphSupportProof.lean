module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem packedInnerValue (d e payload inner : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner d payload))) :
    Nonempty (Derivation body Delta
      (graph3 (pairOf (.projection 0) (.projection 2)) inner d e payload)) :=
  binaryValue InternalPairing.pairing (.projection 0) (.projection 2) inner d payload
    (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) hi
    (projectionValue 0 (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))))
    (projectionValue 2 (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))))

theorem packedNodeValue (d e payload inner node : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner d payload)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node (numeral 1) inner))) :
    Nonempty (Derivation body Delta
      (graph3 (pairOf (InternalLessThan.constantOne 3) (pairOf (.projection 0) (.projection 2)))
        node d e payload)) :=
  binaryValue InternalPairing.pairing (InternalLessThan.constantOne 3)
    (pairOf (.projection 0) (.projection 2)) node (numeral 1) inner
    (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) hn
    (InternalLessThanSupportProof.oneConstantValue _)
    (packedInnerValue d e payload inner hi)

theorem packedArrowValue (d e payload arrowCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 arrow arrowCode d e))) :
    Nonempty (Derivation body Delta
      (graph3 (consOf (.projection 0) (.projection 1)) arrowCode d e payload)) :=
  binaryValue InternalListCodec.consCode (.projection 0) (.projection 1) arrowCode d e
    (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) ha
    (projectionValue 0 (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))))
    (projectionValue 1 (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))))

theorem packedAtPairs (out d e payload arrowCode inner node : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 arrow arrowCode d e)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner d payload)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node (numeral 1) inner)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out arrowCode node))) :
    Nonempty (Derivation body Delta (graph3 packedLambda out d e payload)) :=
  binaryValue InternalPairing.pairing (consOf (.projection 0) (.projection 1))
    (pairOf (InternalLessThan.constantOne 3) (pairOf (.projection 0) (.projection 2)))
    out arrowCode node (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) ho
    (packedArrowValue d e payload arrowCode ha) (packedNodeValue d e payload inner node hi hn)

theorem packedOuter (out d e payload arrowCode inner node : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 arrow arrowCode d e)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner d payload)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node (numeral 1) inner)))
    (hp : Nonempty (Derivation body Delta (graph3 packedLambda out d e payload))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out arrowCode node)) :=
  binaryRecover InternalPairing.pairing (consOf (.projection 0) (.projection 1))
    (pairOf (InternalLessThan.constantOne 3) (pairOf (.projection 0) (.projection 2)))
    out arrowCode node (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) hp
    (packedArrowValue d e payload arrowCode ha) (packedNodeValue d e payload inner node hi hn)

/-- Each selector follows the original nested pairs. No arithmetic truth or
native evaluation is reflected into the object-language derivation. -/
theorem selectorsAtPairs (out d payload arrowCode inner node : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner d payload)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node (numeral 1) inner)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out arrowCode node))) :
    Nonempty (Derivation body Delta
      (graph1 tag (numeral 1) out ⊓
        (graph1 InternalUnpair.left arrowCode out ⊓
          (graph1 domain d out ⊓ graph1 bodyPayload payload out)))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons out Fin.elim0
  have hnode := unaryValue InternalUnpair.right (.projection 0) node out xs
    (pairRight out arrowCode node ho) (projectionValue 0 xs)
  have hinner := unaryValue InternalUnpair.right (rightOf (.projection 0)) inner node xs
    (pairRight node (numeral 1) inner hn) hnode
  have ht := unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 1) node xs
    (pairLeft node (numeral 1) inner hn) hnode
  have hd := unaryValue InternalUnpair.left (rightOf (rightOf (.projection 0))) d inner xs
    (pairLeft inner d payload hi) hinner
  have hp := unaryValue InternalUnpair.right (rightOf (rightOf (.projection 0))) payload inner xs
    (pairRight inner d payload hi) hinner
  exact andIntro ht (andIntro (pairLeft out arrowCode node ho) (andIntro hd hp))

theorem bodyCodeValue (b e out payload : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing b e payload)))
    (hp : Nonempty (Derivation body Delta (graph1 bodyPayload payload out))) :
    Nonempty (Derivation body Delta (graph2 bodyCode b e out)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons e (Fin.cons out Fin.elim0)
  exact binaryValue InternalPairing.pairing (.projection 0)
    (.composition bodyPayload (fun _ : Fin 1 => .projection 1)) b e payload xs hb
    (projectionValue 0 xs) (unaryValue bodyPayload (.projection 1) payload out xs hp (projectionValue 1 xs))

theorem bodyCodeRecover (b e out payload : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph2 bodyCode b e out)))
    (hp : Nonempty (Derivation body Delta (graph1 bodyPayload payload out))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing b e payload)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons e (Fin.cons out Fin.elim0)
  exact binaryRecover InternalPairing.pairing (.projection 0)
    (.composition bodyPayload (fun _ : Fin 1 => .projection 1)) b e payload xs hb
    (projectionValue 0 xs) (unaryValue bodyPayload (.projection 1) payload out xs hp (projectionValue 1 xs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
