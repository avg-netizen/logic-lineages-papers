module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaTraversal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Bind the traversal's actual repacked body to the original binary selector. -/
theorem bodyCodeAt (raw e child : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 rawBody child raw))) :
    Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.bodyCode child e raw)) :=
  binaryRecover OriginalLambdaConstructor.bodyCode rawCodomain (.projection 0)
    child e raw (Fin.cons raw Fin.elim0) hb he (projectionValue 0 (Fin.cons raw Fin.elim0))

/-- The selected body always has exactly the selected codomain as its type. -/
theorem bodyType (raw e child : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 rawBody child raw))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left e child)) := by
  apply programCases OriginalLambdaConstructor.bodyPayload (Fin.cons raw Fin.elim0) _
  intro beta j Theta payload hj hp
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hp
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at he' hb'
  exact pairLeft (child.relabel j) (e.relabel j) payload
    (bodyCodeRecover (child.relabel j) (e.relabel j) (raw.relabel j) payload
      (bodyCodeAt (raw.relabel j) (e.relabel j) (child.relabel j) he' hb') hp)

/-- Only the actual payload domain determines the extension of Gamma.
Changing the body, tag or outer type cannot change this parameter. -/
theorem childParameterCongr (raw rebuilt d parameter bodyParameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 rawDomain d raw)))
    (hr : Nonempty (Derivation body Delta (graph1 rawDomain d rebuilt)))
    (hp : Nonempty (Derivation body Delta (graph2 childParameter bodyParameter raw parameter))) :
    Nonempty (Derivation body Delta (graph2 childParameter bodyParameter rebuilt parameter)) := by
  let context : Program 2 := leftOf (.projection 1)
  let gamma : Program 2 := rightOf (.projection 1)
  let domain : Program 2 := .composition rawDomain (fun _ : Fin 1 => .projection 0)
  let extended : Program 2 := consOf domain gamma
  let qs : Fin 3 → Program 2 := ![context,gamma,extended]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  have hd' := renameInto hd j Theta hj
  have hr' := renameInto hr j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hd' hr'
  rw [graph2Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let rr : Fin 2 → OTerm beta := Fin.cons (rebuilt.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hdv := unaryValue rawDomain (.projection 0) (d.relabel j) (raw.relabel j) xx
    hd' (projectionValue 0 xx)
  have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) xx
    (hq 0) (projectionValue 1 xx)
  have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx
    (hq 1) (projectionValue 1 xx)
  have he := binaryRecover InternalListCodec.consCode domain gamma (ys 2) (d.relabel j) (ys 1) xx
    (hq 2) hdv (hq 1)
  have hpair := binaryRecover InternalPairing.pairing context extended
    (bodyParameter.relabel j) (ys 0) (ys 2) xx hp' (hq 0) (hq 2)
  have hcr := unaryValue InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) rr
    hc (projectionValue 1 rr)
  have hgr := unaryValue InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) rr
    hg (projectionValue 1 rr)
  have hdr := unaryValue rawDomain (.projection 0) (d.relabel j) (rebuilt.relabel j) rr
    hr' (projectionValue 0 rr)
  have her := binaryValue InternalListCodec.consCode domain gamma (ys 2) (d.relabel j) (ys 1) rr
    he hdr hgr
  exact binaryValue InternalPairing.pairing context extended
    (bodyParameter.relabel j) (ys 0) (ys 2) rr hpair hcr her

/-- The extension preserves the SAME outer context, without decoding Gamma. -/
theorem childContext (raw parameter bodyParameter contextCode : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 childParameter bodyParameter raw parameter)))
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left contextCode parameter))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left contextCode bodyParameter)) := by
  let extended : Program 2 := consOf
    (.composition rawDomain (fun _ : Fin 1 => .projection 0)) (rightOf (.projection 1))
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply programCases extended xs _
  intro beta j Theta gamma hj hg
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hp'
  rw [graph1Rename] at hc'
  simp only [xs,consTermRename,emptyRename] at hg
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  exact pairLeft (bodyParameter.relabel j) (contextCode.relabel j) gamma
    (binaryRecover InternalPairing.pairing (leftOf (.projection 1)) extended
      (bodyParameter.relabel j) (contextCode.relabel j) gamma xx hp'
      (unaryValue InternalUnpair.left (.projection 1) (contextCode.relabel j) (parameter.relabel j) xx
        hc' (projectionValue 1 xx)) hg)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
