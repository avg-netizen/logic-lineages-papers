module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalListCodecSupportProof (consGraph consGraphRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph scan decorate

theorem twoCells (F : Program 1)
    (role typ raw jobs annotatedPrefix row first resultTail second mark0 mark1 raw0 raw1 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph5 scan annotatedPrefix (numeral 2) role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (consGraph row first resultTail)))
    (ht : Nonempty (Derivation body Delta (consGraph resultTail second z)))
    (hc0 : Nonempty (Derivation body Delta (graph5 cell mark0 z role typ raw jobs)))
    (hc1 : Nonempty (Derivation body Delta (graph5 cell mark1 (numeral 1) role typ raw jobs)))
    (hl0 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup raw0 z jobs)))
    (hl1 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup raw1 (numeral 1) jobs))) :
    Nonempty (Derivation body Delta ((graph1 F first mark0) ⊓ (graph1 F second mark1))) := by
  let scanOne : Program 6 := .composition scan
    ![OriginalRawSyntaxTransport.constant 6 1,.projection 0,.projection 1,.projection 2,.projection 3]
  let single0 : Program 6 := OriginalHereditaryExpansion.consOf (.projection 4) (OriginalRawSyntaxTransport.constant 6 0)
  let single1 : Program 6 := OriginalHereditaryExpansion.consOf (.projection 5) (OriginalRawSyntaxTransport.constant 6 0)
  let qs : Fin 3 → Program 6 := ![scanOne,single0,single1]
  let xs : Fin 6 → OTerm alpha := ![role,typ,raw,jobs,mark0,mark1]
  apply queryCases qs xs _
  intro beta rho ys Theta hinc hq
  simp only [conjunctionRename,graph1Rename]
  let xx : Fin 6 → OTerm beta := ![role.relabel rho,typ.relabel rho,raw.relabel rho,jobs.relabel rho,mark0.relabel rho,mark1.relabel rho]
  have hx : (fun i => (xs i).relabel rho) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
  rw [hx] at hq
  have hp' := renameInto hp rho Theta hinc
  have hm' := renameInto hm rho Theta hinc
  have hr' := renameInto hr rho Theta hinc
  have ht' := renameInto ht rho Theta hinc
  have hc0' := renameInto hc0 rho Theta hinc
  have hc1' := renameInto hc1 rho Theta hinc
  have hl0' := renameInto hl0 rho Theta hinc
  have hl1' := renameInto hl1 rho Theta hinc
  simp only [graph1Rename,graph2Rename,graph5Rename,consGraphRename,zRelabel,
    GuardedSourceSyntaxProof.numeralRename] at hp' hm' hr' ht' hc0' hc1' hl0' hl1'
  have hs0 := binaryRecover InternalListCodec.consCode (.projection 4) (OriginalRawSyntaxTransport.constant 6 0)
    (ys 1) (mark0.relabel rho) z xx (hq 1) (projectionValue 4 xx) (constantValue 0 xx)
  have hs1 := binaryRecover InternalListCodec.consCode (.projection 5) (OriginalRawSyntaxTransport.constant 6 0)
    (ys 2) (mark1.relabel rho) z xx (hq 2) (projectionValue 5 xx) (constantValue 0 xx)
  have hprev : Nonempty (Derivation body Theta (graph5 scan (ys 0) (numeral 1)
      (role.relabel rho) (typ.relabel rho) (raw.relabel rho) (jobs.relabel rho))) := by
    apply compositionRecover scan _ (ys 0) xx
      (Fin.cons (numeral 1) (Fin.cons (role.relabel rho) (Fin.cons (typ.relabel rho)
        (Fin.cons (raw.relabel rho) (Fin.cons (jobs.relabel rho) Fin.elim0))))) (hq 0)
    intro i
    exact Fin.cases (constantValue 1 xx) (Fin.cases (projectionValue 0 xx)
      (Fin.cases (projectionValue 1 xx) (Fin.cases (projectionValue 2 xx)
        (Fin.cases (projectionValue 3 xx) (fun k => Fin.elim0 k))))) i
  exact ChildScanCoreProof.atValues F (role.relabel rho) (typ.relabel rho) (raw.relabel rho)
    (jobs.relabel rho) (annotatedPrefix.relabel rho) (row.relabel rho) (first.relabel rho)
    (resultTail.relabel rho) (second.relabel rho) (mark0.relabel rho) (mark1.relabel rho)
    (raw0.relabel rho) (raw1.relabel rho) (ys 0) (ys 1) (ys 2)
    hp' hm' hr' ht' hc0' hc1' hl0' hl1' hprev hs0 hs1
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
