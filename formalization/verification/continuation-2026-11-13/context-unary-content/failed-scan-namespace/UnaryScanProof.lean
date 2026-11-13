module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof (compositionRecover)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalListCodecSupportProof (consGraph consGraphRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph scan decorate

theorem atSingleton (F : Program 1)
    (role typ raw jobs annotatedPrefix row first mark rawCell singleton : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph5 scan annotatedPrefix (numeral 1) role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (consGraph row first z)))
    (hc : Nonempty (Derivation body Delta (graph5 cell mark z role typ raw jobs)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell z jobs)))
    (hs : Nonempty (Derivation body Delta (consGraph singleton mark z))) :
    Nonempty (Derivation body Delta (graph1 F first mark)) := by
  have ha := NarrowScanAppendProof.scanAppendAtLookup z z role typ raw jobs mark singleton annotatedPrefix rawCell
    (ChildScanCoreProof.scanZero role typ raw jobs) hp hc hs hl
  obtain ⟨he⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover annotatedPrefix singleton ha
  have hpcons := outputTransport InternalListCodec.consCode singleton annotatedPrefix
    (Fin.cons mark (Fin.cons z Fin.elim0)) ⟨InternalTagArithmeticSupportProof.symm he⟩ hs
  exact InternalApplicationStepPeelSupportProof.andLeft
    (ChildMapRecoverProof.recover F annotatedPrefix mark z first z row hpcons hr hm)

theorem oneCell (F : Program 1)
    (role typ raw jobs annotatedPrefix row first mark rawCell : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph5 scan annotatedPrefix (numeral 1) role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (consGraph row first z)))
    (hc : Nonempty (Derivation body Delta (graph5 cell mark z role typ raw jobs)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell z jobs))) :
    Nonempty (Derivation body Delta (graph1 F first mark)) := by
  let P : Program 1 := OriginalHereditaryExpansion.consOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)
  let xs : Fin 1 → OTerm alpha := Fin.cons mark Fin.elim0
  apply programCases P xs _
  intro beta rho Theta singleton hinc hs
  rw [graph1Rename]
  let xx : Fin 1 → OTerm beta := Fin.cons (mark.relabel rho) Fin.elim0
  have hx : (fun i => (xs i).relabel rho) = xx := by
    funext i
    exact Fin.cases rfl (fun k => Fin.elim0 k) i
  rw [hx] at hs
  have hsingle := binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)
    singleton (mark.relabel rho) z xx hs (projectionValue 0 xx) (constantValue 0 xx)
  have hp' := renameInto hp rho Theta hinc
  have hm' := renameInto hm rho Theta hinc
  have hr' := renameInto hr rho Theta hinc
  have hc' := renameInto hc rho Theta hinc
  have hl' := renameInto hl rho Theta hinc
  simp only [graph1Rename,graph2Rename,graph5Rename,consGraphRename,zRelabel,
    GuardedSourceSyntaxProof.numeralRename] at hp' hm' hr' hc' hl'
  exact atSingleton F (role.relabel rho) (typ.relabel rho) (raw.relabel rho) (jobs.relabel rho)
    (annotatedPrefix.relabel rho) (row.relabel rho) (first.relabel rho) (mark.relabel rho)
    (rawCell.relabel rho) singleton hp' hm' hr' hc' hl' hsingle
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryScanProof
