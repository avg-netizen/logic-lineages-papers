module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSupportProof (consHead consTail)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map

theorem atValues (F : Program 1) (code head tail mappedHead mappedTail out u v : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out mappedHead mappedTail)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out code)))
    (hu : Nonempty (Derivation body Delta (graph1 F u head)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) v tail))) :
    Nonempty (Derivation body Delta ((graph1 F mappedHead head) ⊓
      (graph1 (InternalListMap.map (k := 0) F) mappedTail tail))) := by
  have hcons := InternalListMapProof.consForward F code head tail u v out Fin.elim0 hc hu hv hm
  have heh := valueUnique InternalListCodec.headCode u mappedHead (Fin.cons out Fin.elim0)
    (consHead out u v hcons) (consHead out mappedHead mappedTail ho)
  have het := valueUnique InternalListCodec.tailCode v mappedTail (Fin.cons out Fin.elim0)
    (consTail out u v hcons) (consTail out mappedHead mappedTail ho)
  exact andIntro (outputTransport F u mappedHead (Fin.cons head Fin.elim0) heh hu)
    (outputTransport (InternalListMap.map (k := 0) F) v mappedTail (Fin.cons tail Fin.elim0) het hv)

theorem recover (F : Program 1) (code head tail mappedHead mappedTail out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out mappedHead mappedTail)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out code))) :
    Nonempty (Derivation body Delta ((graph1 F mappedHead head) ⊓
      (graph1 (InternalListMap.map (k := 0) F) mappedTail tail))) := by
  let qs : Fin 2 → Program 2 := ![.composition F (fun _ : Fin 1 => .projection 0),
    .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons head (Fin.cons tail Fin.elim0)
  apply queryCases qs xs _
  intro beta rho ys Theta hinc hq
  simp only [conjunctionRename,graph1Rename]
  let xx : Fin 2 → OTerm beta := Fin.cons (head.relabel rho) (Fin.cons (tail.relabel rho) Fin.elim0)
  have hx : (fun i => (xs i).relabel rho) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hx] at hq
  have hc' := renameInto hc rho Theta hinc
  have ho' := renameInto ho rho Theta hinc
  have hm' := renameInto hm rho Theta hinc
  simp only [consGraphRename,graph1Rename] at hc' ho' hm'
  have hu := unaryRecover F (.projection 0) (ys 0) (head.relabel rho) xx (hq 0) (projectionValue 0 xx)
  have hv := unaryRecover (InternalListMap.map (k := 0) F) (.projection 1) (ys 1) (tail.relabel rho) xx (hq 1) (projectionValue 1 xx)
  exact atValues F (code.relabel rho) (head.relabel rho) (tail.relabel rho)
    (mappedHead.relabel rho) (mappedTail.relabel rho) (out.relabel rho) (ys 0) (ys 1) hc' ho' hm' hu hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
