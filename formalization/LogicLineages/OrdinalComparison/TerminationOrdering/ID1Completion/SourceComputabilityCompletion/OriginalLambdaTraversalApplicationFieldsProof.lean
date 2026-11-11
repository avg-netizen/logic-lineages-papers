module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversal OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem fieldsRename {beta : Type} (parent d e fn arg : OTerm alpha) (j : alpha → beta) :
    (ApplicationFields parent d e fn arg).relabel j =
      ApplicationFields (parent.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) := by
  simp only [ApplicationFields,conjunctionRename,graph1Rename,
    SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]

/-- The legacy function selector composes LEFT with projection; the new
raw selector uses the literal unary LEFT AST. Transport this difference by
internal composition graphs, never by equality of native evaluations. -/
theorem functionSelector (parent fn d e : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (graph1 InternalCanonicalResultFoldOpening.functionChild fn parent)))
    (hd : Nonempty (Derivation body Delta (graph1 rawDomain d parent)))
    (he : Nonempty (Derivation body Delta (graph1 rawType e parent))) :
    Nonempty (Derivation body Delta (graph1 rawFunction fn parent)) := by
  let arrowP := consOf rawDomain rawType
  let payloadP := InternalApplicationStepPeel.functionPayload (.projection 0)
  let qs : Fin 2 → Program 1 := ![arrowP,payloadP]
  apply InternalApplicationStepPeelSupportProof.queryCases qs (Fin.cons parent Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hf' := renameInto hf j Theta hj
  have hd' := renameInto hd j Theta hj
  have he' := renameInto he j Theta hj
  rw [graph1Rename] at hf' hd' he'
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have harrow := binaryRecover InternalListCodec.consCode rawDomain rawType
    (ys 0) (d.relabel j) (e.relabel j) xs (hq 0) hd' he'
  have oldType : Nonempty (Derivation body Theta
      (graph1 InternalCanonicalResultFoldOpening.rootCodomain (e.relabel j) (parent.relabel j))) :=
    unaryValue InternalUnpair.left (.projection 0) (e.relabel j) (parent.relabel j) xs
      he' (projectionValue 0 xs)
  have oldArrow := binaryValue InternalListCodec.consCode
    InternalCanonicalResultFoldOpening.rootDomain InternalCanonicalResultFoldOpening.rootCodomain
      (ys 0) (d.relabel j) (e.relabel j) xs harrow hd' oldType
  have pair := binaryRecover InternalPairing.pairing
    (consOf InternalCanonicalResultFoldOpening.rootDomain InternalCanonicalResultFoldOpening.rootCodomain)
    payloadP (fn.relabel j) (ys 0) (ys 1) xs hf' oldArrow (hq 1)
  exact binaryValue InternalPairing.pairing arrowP payloadP (fn.relabel j)
    (ys 0) (ys 1) xs pair (hq 0) (hq 1)

/-- Exact traversal selectors at the existing original constructor block. -/
theorem fromConstructors (arrow d e fp ap fn arg parent : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent))) :
    Nonempty (Derivation body Delta (ApplicationFields parent d e fn arg)) := by
  have root := OriginalConstructorShapeApplicationProof.packedFields d e fp ap parent
    (andRight (andRight (andRight hc)))
  have children := InternalParameterizedCanonicalResultFoldOpeningProof.selectorGraphs
    arrow d e fp ap fn arg parent hc
  have ht := InternalCanonicalResultFoldInvariantApplicationSupportProof.packedLeft
    d e fp ap parent (andRight (andRight (andRight hc)))
  have hf := functionSelector parent fn d e (andLeft children) (andRight root) ht
  exact andIntro (andLeft root) (andIntro (andRight root)
    (andIntro ht (andIntro hf (andLeft (andRight children)))))

/-- The reconstructed children are literally the supplied typed outputs,
not merely terms sharing their raw payloads. Both output payload witnesses
are selected internally, then the actual child selectors are recovered. -/
theorem fromRaw (arrow d e fn arg parent : OTerm alpha)
    (harrow : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)))
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg))) :
    Nonempty (Derivation body Delta (ApplicationFields parent d e fn arg)) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons fn (Fin.cons arg Fin.elim0)
  apply InternalApplicationStepPeelSupportProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [fieldsRename]
  have harrow' := renameInto harrow j Theta hj
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at harrow'
  rw [graph1Rename] at hf' ha'
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) Fin.elim0)
  have hfp := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (fn.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have hap := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (arg.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have packed := applicationForward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (ys 0) (ys 1) (parent.relabel j) hfp hap hp'
  exact fromConstructors (arrow.relabel j) (d.relabel j) (e.relabel j) (ys 0) (ys 1)
    (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (andIntro harrow' (andIntro (reconstructPair (fn.relabel j) (arrow.relabel j) (ys 0) hf' hfp)
      (andIntro (reconstructPair (arg.relabel j) (d.relabel j) (ys 1) ha' hap) packed)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
