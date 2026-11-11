module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open OriginalLambdaTraversal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Pair destruction for an unchanged composed constructor. Its left output
is obtained internally, so no type-code witness is assumed. -/
 theorem composedPairRight {n : Nat} (p q : Program n) (out payload : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph (pairOf p q) out xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q payload xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload out)) := by
  apply programCases p xs _
  intro beta j Theta value hj hv
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  have hq' := renameInto hq j Theta hj
  rw [programRename] at hp' hq'
  exact pairRight (out.relabel j) value (payload.relabel j)
    (binaryRecover InternalPairing.pairing p q (out.relabel j) value (payload.relabel j)
      (fun i => (xs i).relabel j) hp' hv hq')

 theorem functionPayloadSelected (state fn payload middle children fp : OTerm alpha)
    (hfn : Nonempty (Derivation body Delta (graph1 rawFunction fn state)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload state)))
    (hm : Nonempty (Derivation body Delta (graph1 InternalUnpair.right middle payload)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.right children middle)))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left fp children))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hm' := unaryValue InternalUnpair.right (rightOf (.projection 0)) middle payload xs hm hp
  have hc' := unaryValue InternalUnpair.right (InternalApplicationStepPeel.appBody (.projection 0))
    children middle xs hc hm'
  have hf' := unaryValue InternalUnpair.left (rightOf (InternalApplicationStepPeel.appBody (.projection 0)))
    fp children xs hf hc'
  exact composedPairRight (consOf rawDomain rawType)
    (InternalApplicationStepPeel.functionPayload (.projection 0)) fn fp xs hfn hf'

 theorem argumentPayloadSelected (state arg payload middle children ap : OTerm alpha)
    (harg : Nonempty (Derivation body Delta (graph1 rawArgument arg state)))
    (hp : Nonempty (Derivation body Delta (graph1 (rightOf (.projection 0)) payload state)))
    (hm : Nonempty (Derivation body Delta (graph1 InternalUnpair.right middle payload)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.right children middle)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap children))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hm' := unaryValue InternalUnpair.right (rightOf (.projection 0)) middle payload xs hm hp
  have hc' := unaryValue InternalUnpair.right (InternalApplicationStepPeel.appBody (.projection 0))
    children middle xs hc hm'
  have ha' := unaryValue InternalUnpair.right (rightOf (InternalApplicationStepPeel.appBody (.projection 0)))
    ap children xs ha hc'
  exact composedPairRight rawDomain (InternalApplicationStepPeel.argumentPayload (.projection 0))
    arg ap xs harg ha'

 theorem bodyPayloadSelected (raw child bp : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 rawBody child raw)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.bodyPayload bp raw))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right bp child)) := by
  apply programCases rawCodomain (Fin.cons raw Fin.elim0) _
  intro beta j Theta codomain hj hc
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hc
  have hb' := renameInto hb j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hb' hp'
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hbody := binaryRecover OriginalLambdaConstructor.bodyCode rawCodomain (.projection 0)
    (child.relabel j) codomain (raw.relabel j) xs hb' hc (projectionValue 0 xs)
  let xx : Fin 2 → OTerm beta := Fin.cons codomain (Fin.cons (raw.relabel j) Fin.elim0)
  have hpay := unaryValue OriginalLambdaConstructor.bodyPayload (.projection 1)
    (bp.relabel j) (raw.relabel j) xx hp' (projectionValue 1 xx)
  exact pairRight (child.relabel j) codomain (bp.relabel j)
    (binaryRecover InternalPairing.pairing (.projection 0)
      (.composition OriginalLambdaConstructor.bodyPayload (fun _ : Fin 1 => .projection 1))
      (child.relabel j) codomain (bp.relabel j) xx hbody (projectionValue 0 xx) hpay)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadSelectorProof
