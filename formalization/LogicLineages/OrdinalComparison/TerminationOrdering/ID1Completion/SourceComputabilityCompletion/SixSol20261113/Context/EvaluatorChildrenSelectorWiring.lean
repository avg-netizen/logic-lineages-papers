module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Proof-side graph transfer, not a changed source Program. -/
def Lifted (q : Program 1) (r : Program 2) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (out parent parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 q out parent)) →
 Nonempty (Derivation body Delta (graph2 r out parent parameter))
theorem primitive (q : Program 1) : Lifted q (.composition q (fun _ : Fin 1 => .projection 0)) := by
 intro body alpha Delta out parent parameter h
 exact unaryValue q (.projection 0) out parent ![parent,parameter] h (projectionValue 0 ![parent,parameter])
theorem projection : Lifted (.projection 0) (.projection 0) := by
 intro body alpha Delta out parent parameter h
 have he := valueUnique (.projection (0 : Fin 1)) out parent (Fin.cons parent Fin.elim0)
   h (projectionValue 0 (Fin.cons parent Fin.elim0))
 exact outputTransport (.projection (0 : Fin 2)) parent out ![parent,parameter]
   (by obtain ⟨he⟩ := he; exact ⟨InternalTagArithmeticSupportProof.symm he⟩)
   (projectionValue 0 ![parent,parameter])
theorem composition {k : Nat} (f : Program k) (g : Fin k → Program 1) (h : Fin k → Program 2)
 (ih : ∀ i, Lifted (g i) (h i)) : Lifted (.composition f g) (.composition f h) := by
 intro body alpha Delta out parent parameter hg
 apply queryCases g (Fin.cons parent Fin.elim0) _
 intro beta j ys Theta hj hq
 rw [graph2Rename]
 have hg' := renameInto hg j Theta hj
 rw [graph1Rename] at hg'
 simp only [consTermRename,emptyRename] at hq
 have hf := compositionRecover f g (out.relabel j) (Fin.cons (parent.relabel j) Fin.elim0) ys hg' hq
 exact compositionValue f h (out.relabel j) ![parent.relabel j,parameter.relabel j] ys hf
   (fun i => ih i body beta Theta (ys i) (parent.relabel j) (parameter.relabel j) (hq i))
theorem unary (f : Program 1) {g : Program 1} {h : Program 2} (ih : Lifted g h) :
 Lifted (.composition f (fun _ : Fin 1 => g)) (.composition f (fun _ : Fin 1 => h)) :=
 composition f _ _ (fun _ => ih)
theorem binary (f : Program 2) {a b : Program 1} {c d : Program 2}
 (ha : Lifted a c) (hb : Lifted b d) : Lifted (.composition f ![a,b]) (.composition f ![c,d]) := by
 apply composition
 intro i
 exact Fin.cases ha (Fin.cases hb (fun k => Fin.elim0 k)) i

theorem tag : Lifted OriginalLambdaTraversal.rawTag OriginalRootObservation.tag :=
 unary InternalUnpair.left (unary InternalUnpair.right projection)
theorem domain : Lifted OriginalLambdaTraversal.rawDomain OriginalRootObservation.domain :=
 unary InternalUnpair.left (unary InternalUnpair.right (unary InternalUnpair.right projection))
theorem resultType : Lifted OriginalLambdaTraversal.rawType OriginalRootObservation.resultType := primitive InternalUnpair.left
theorem codomain : Lifted OriginalLambdaTraversal.rawCodomain OriginalRootObservation.codomain :=
 unary InternalListCodec.tailCode resultType
theorem bodyPayload : Lifted OriginalLambdaConstructor.bodyPayload (rightOf OriginalRootObservation.payload) :=
 unary InternalUnpair.right (unary InternalUnpair.right (unary InternalUnpair.right projection))
theorem function : Lifted OriginalLambdaTraversal.rawFunction OriginalRootObservation.functionPacked :=
 binary InternalPairing.pairing (binary InternalListCodec.consCode domain resultType)
   (unary InternalUnpair.left (unary InternalUnpair.right (unary InternalUnpair.right (unary InternalUnpair.right projection))))
theorem argument : Lifted OriginalLambdaTraversal.rawArgument OriginalRootObservation.argumentPacked :=
 binary InternalPairing.pairing domain
   (unary InternalUnpair.right (unary InternalUnpair.right (unary InternalUnpair.right (unary InternalUnpair.right projection))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
