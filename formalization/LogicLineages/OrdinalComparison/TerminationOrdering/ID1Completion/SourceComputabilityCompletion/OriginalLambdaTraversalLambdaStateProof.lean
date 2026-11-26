module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaTraversalLambdaSelectorProof
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalChildSyntaxProof
open OriginalTransparentLambdaFinalChildSupportProof
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalExtensionProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Relate the traversal body to the independent hereditary validator's
actual state selector. No evaluator or successful validator run is used. -/
theorem bodyAtState (state raw e child : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryValidity.currentRaw raw state)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child raw))) :
    Nonempty (Derivation body Delta (graph1 OriginalHereditaryValidity.currentBody child state)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta typ hj ht
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at ht
  have hr' := renameInto hr j Theta hj
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at hr' he' hb'
  let rr : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  let ss : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have htstate := unaryValue InternalUnpair.left OriginalHereditaryValidity.currentRaw
    typ (raw.relabel j) ss ht hr'
  have hetail := unaryRecover InternalListCodec.tailCode OriginalLambdaTraversal.rawType
    (e.relabel j) typ rr he' ht
  have hestate := unaryValue InternalListCodec.tailCode OriginalHereditaryValidity.currentType
    (e.relabel j) typ ss hetail htstate
  exact binaryValue OriginalLambdaConstructor.bodyCode OriginalHereditaryValidity.currentCodomain
    OriginalHereditaryValidity.currentRaw (child.relabel j) (e.relabel j) (raw.relabel j) ss
    (bodyCodeAt (raw.relabel j) (e.relabel j) (child.relabel j) he' hb') hestate hr'

/-- The traversal parameter agrees with the independent validator's actual
state extension, retaining its original encoded Gamma and outer context. -/
theorem parameterAtState (state raw parameter bodyParameter : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryValidity.currentRaw raw state)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryValidity.currentParameter parameter state)))
    (hb : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter))) :
    Nonempty (Derivation body Delta
      (graph1 OriginalHereditaryValidity.childParameter bodyParameter state)) := by
  let context : Program 2 := leftOf (.projection 1)
  let gamma : Program 2 := rightOf (.projection 1)
  let domain : Program 2 := .composition OriginalLambdaTraversal.rawDomain (fun _ : Fin 1 => .projection 0)
  let extended : Program 2 := consOf domain gamma
  let qs : Fin 4 → Program 2 := ![context,gamma,domain,extended]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hr' := renameInto hr j Theta hj
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at hr' hp'
  rw [graph2Rename] at hb'
  simp only [xs,consTermRename,emptyRename] at hq
  let rr : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let ss : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) rr
    (hq 0) (projectionValue 1 rr)
  have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) rr
    (hq 1) (projectionValue 1 rr)
  have hd := unaryRecover OriginalLambdaConstructor.domain (.projection 0) (ys 2) (raw.relabel j) rr
    (hq 2) (projectionValue 0 rr)
  have he := binaryRecover InternalListCodec.consCode domain gamma (ys 3) (ys 2) (ys 1) rr
    (hq 3) (hq 2) (hq 1)
  have hpair := binaryRecover InternalPairing.pairing context extended
    (bodyParameter.relabel j) (ys 0) (ys 3) rr hb' (hq 0) (hq 3)
  have hcs := unaryValue InternalUnpair.left OriginalHereditaryValidity.currentParameter
    (ys 0) (parameter.relabel j) ss hc hp'
  have hgs := unaryValue InternalUnpair.right OriginalHereditaryValidity.currentParameter
    (ys 1) (parameter.relabel j) ss hg hp'
  have hds := unaryValue OriginalLambdaConstructor.domain OriginalHereditaryValidity.currentRaw
    (ys 2) (raw.relabel j) ss hd hr'
  have hes := binaryValue InternalListCodec.consCode OriginalHereditaryValidity.currentDomain
    (rightOf OriginalHereditaryValidity.currentParameter) (ys 3) (ys 2) (ys 1) ss he hds hgs
  exact binaryValue InternalPairing.pairing (leftOf OriginalHereditaryValidity.currentParameter)
    (consOf OriginalHereditaryValidity.currentDomain (rightOf OriginalHereditaryValidity.currentParameter))
    (bodyParameter.relabel j) (ys 0) (ys 3) ss hpair hcs hes

/-- Eliminate the original final-child witness block at exactly the traversal's
body and parameter, rather than assuming the witnesses coincide. -/
theorem finalChildAtSelectors (valid : Program 2) (raw e child parameter bodyParameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child raw)))
    (hp : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter)))
    (hf : Nonempty (Derivation body Delta (FinalLambdaChild valid raw parameter))) :
    Nonempty (Derivation body Delta (graph2 valid (numeral 1) child bodyParameter)) := by
  apply programCases OriginalHereditaryValidity.initial (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta state hj hi
  simp only [graph2Rename,oneRename]
  simp only [consTermRename,emptyRename] at hi
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  have hp' := renameInto hp j Theta hj
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at he' hb'
  rw [graph2Rename] at hp'
  rw [finalChildRename] at hf'
  have hs := initialSelectors state (raw.relabel j) (parameter.relabel j) hi
  exact finalChildAt valid (raw.relabel j) (parameter.relabel j) state
    (child.relabel j) (bodyParameter.relabel j) hi
    (bodyAtState state (raw.relabel j) (e.relabel j) (child.relabel j) (andLeft hs) he' hb')
    (parameterAtState state (raw.relabel j) (parameter.relabel j) (bodyParameter.relabel j)
      (andLeft hs) (andRight hs) hp') hf'

/-- Reconstruct the original child witness block from the actual selector
values and SAME validator acceptance. The extension witness is proved. -/
theorem finalChildFromSelectors (valid : Program 2) (raw e child parameter bodyParameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e raw)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawBody child raw)))
    (hp : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 valid (numeral 1) child bodyParameter))) :
    Nonempty (Derivation body Delta (FinalLambdaChild valid raw parameter)) := by
  apply programCases OriginalHereditaryValidity.initial (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta state hj hi
  rw [finalChildRename]
  simp only [consTermRename,emptyRename] at hi
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  have hp' := renameInto hp j Theta hj
  have hv' := renameInto hv j Theta hj
  rw [graph1Rename] at he' hb'
  rw [graph2Rename] at hp'
  simp only [graph2Rename,oneRename] at hv'
  have hs := initialSelectors state (raw.relabel j) (parameter.relabel j) hi
  have hbody := bodyAtState state (raw.relabel j) (e.relabel j) (child.relabel j)
    (andLeft hs) he' hb'
  have hparameter := parameterAtState state (raw.relabel j) (parameter.relabel j)
    (bodyParameter.relabel j) (andLeft hs) (andRight hs) hp'
  have hext := childParameterExtension state (raw.relabel j) (parameter.relabel j)
    (bodyParameter.relabel j) (andLeft hs) (andRight hs) hparameter
  exact finalChildIntro valid (raw.relabel j) (parameter.relabel j) state
    (child.relabel j) (bodyParameter.relabel j)
    (andIntro hi (andIntro (andIntro hbody hext) (andIntro hparameter hv')))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaStateProof
