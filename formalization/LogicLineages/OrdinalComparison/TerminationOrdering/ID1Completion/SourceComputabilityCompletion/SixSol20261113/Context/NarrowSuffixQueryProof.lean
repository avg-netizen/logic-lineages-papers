module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowSuffixStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowSuffixQueryProof
open SixSol20261112.Context
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open OriginalInternalJobDeletionLookupProof (bumpRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open AnnotationSuffixSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map OriginalHereditaryAnnotatedExpansion.scan
  InternalApplicationValidityStackAppend.append OriginalContextInsertion.length InternalListCodec.consCode

theorem consCore (arity : Nat)
    (suffix head tail offset typ raw front jobs annotatedFront count full mapped : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph suffix head tail)))
    (hi : Nonempty (Derivation body Delta (row arity tail)))
    (hf : Nonempty (Derivation body Delta (fields arity suffix offset typ raw front jobs annotatedFront count full mapped))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped)) := by
  let p0 : Program 7 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 1)
  let p1 : Program 7 := .composition InheritedMapDefinitions.inheritedJob ![.projection 0,.projection 2]
  let p2 : Program 7 := .composition (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) ![.projection 1,.projection 2]
  let p3 : Program 7 := consOf (.projection 0) (OriginalRawSyntaxTransport.constant 7 0)
  let p4 : Program 7 := consOf p1 (OriginalRawSyntaxTransport.constant 7 0)
  let p5 : Program 7 := .composition InternalApplicationValidityStackAppend.append ![.projection 3,p3]
  let index : Program 7 := .composition .succ (fun _ : Fin 1 => .projection 6)
  let p6 : Program 7 := .composition OriginalHereditaryAnnotatedExpansion.scan
    ![index,OriginalRawSyntaxTransport.constant 7 0,.projection 2,.projection 5,.projection 4]
  let p7 : Program 7 := .composition InternalApplicationValidityStackAppend.append ![p5,.projection 1]
  let qs : Fin 8 → Program 7 := ![p0,p1,p2,p3,p4,p5,p6,p7]
  let xs : Fin 7 → OTerm alpha := ![head,tail,typ,front,jobs,raw,bump arity offset]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let start := bump arity (offset.relabel j)
  let xx : Fin 7 → OTerm beta := ![head.relabel j,tail.relabel j,typ.relabel j,front.relabel j,
    jobs.relabel j,raw.relabel j,start]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))))) i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact bumpRename arity offset j
  rw [hx] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph p0 (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph p1 (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph p2 (ys 2) xx)) := hq 2
  have q3 : Nonempty (Derivation body Theta (programGraph p3 (ys 3) xx)) := hq 3
  have q4 : Nonempty (Derivation body Theta (programGraph p4 (ys 4) xx)) := hq 4
  have q5 : Nonempty (Derivation body Theta (programGraph p5 (ys 5) xx)) := hq 5
  have q6 : Nonempty (Derivation body Theta (programGraph p6 (ys 6) xx)) := hq 6
  have q7 : Nonempty (Derivation body Theta (programGraph p7 (ys 7) xx)) := hq 7
  have ht := unaryRecover OriginalContextInsertion.length (.projection 1)
    (ys 0) (tail.relabel j) xx q0 (projectionValue 1 xx)
  have hh := binaryRecover InheritedMapDefinitions.inheritedJob (.projection 0) (.projection 2)
    (ys 1) (head.relabel j) (typ.relabel j) xx q1 (projectionValue 0 xx) (projectionValue 2 xx)
  have hm := binaryRecover (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) (.projection 1) (.projection 2)
    (ys 2) (tail.relabel j) (typ.relabel j) xx q2 (projectionValue 1 xx) (projectionValue 2 xx)
  have hsr := binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 7 0)
    (ys 3) (head.relabel j) z xx q3 (projectionValue 0 xx) (constantValue 0 xx)
  have hsa := binaryRecover InternalListCodec.consCode p1 (OriginalRawSyntaxTransport.constant 7 0)
    (ys 4) (ys 1) z xx q4 q1 (constantValue 0 xx)
  have hg := binaryRecover InternalApplicationValidityStackAppend.append (.projection 3) p3
    (ys 5) (front.relabel j) (ys 3) xx q5 (projectionValue 3 xx) q3
  have hv : Nonempty (Derivation body Theta (programGraph index (suc start) xx)) :=
    unaryValue .succ (.projection 6) (suc start) start xx
      (successorValue (Fin.cons start Fin.elim0)) (projectionValue 6 xx)
  have hn : Nonempty (Derivation body Theta
      (graph5 OriginalHereditaryAnnotatedExpansion.scan (ys 6) (suc start) z
        (typ.relabel j) (raw.relabel j) (jobs.relabel j))) := by
    apply compositionRecover OriginalHereditaryAnnotatedExpansion.scan
      ![index,OriginalRawSyntaxTransport.constant 7 0,.projection 2,.projection 5,.projection 4]
      (ys 6) xx ![suc start,z,typ.relabel j,raw.relabel j,jobs.relabel j] q6
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) i
    · exact hv
    · exact constantValue 0 xx
    · exact projectionValue 2 xx
    · exact projectionValue 5 xx
    · exact projectionValue 4 xx
  have hra := binaryRecover InternalApplicationValidityStackAppend.append p5 (.projection 1)
    (ys 7) (ys 5) (tail.relabel j) xx q7 q5 (projectionValue 1 xx)
  have hc' := renameInto hc j Theta hj
  rw [consGraphRename] at hc'
  have hi' := renameInto hi j Theta hj
  rw [AnnotationSuffixSyntaxProof.rowRename] at hi'
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  exact NarrowSuffixStepProof.atValues arity (suffix.relabel j) (offset.relabel j) (typ.relabel j)
    (raw.relabel j) (front.relabel j) (jobs.relabel j) (annotatedFront.relabel j) (count.relabel j)
    (full.relabel j) (mapped.relabel j) (head.relabel j) (tail.relabel j) (ys 0) (ys 1) (ys 2)
    (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hc' hi' hf' ht hh hm hsr hsa hg hn hra

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowSuffixQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowSuffixQueryProof
