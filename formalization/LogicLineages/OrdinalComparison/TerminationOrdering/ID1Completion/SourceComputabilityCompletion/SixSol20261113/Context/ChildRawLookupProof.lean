module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildRawLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atRows (raw parameter jobs first second children suffix singleton middle : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs children raw parameter)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs children suffix)))
    (ht : Nonempty (Derivation body Delta (consGraph singleton second z)))
    (hm : Nonempty (Derivation body Delta (consGraph middle second suffix))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup first z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup second (numeral 1) jobs))) := by
  have hchildren := OriginalHereditaryInternalExpansionChildrenProof.binaryCons
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) children first second singleton ha hc hf hs ht
  have hrow := OriginalHereditaryInternalFinitePrefixAppendProof.binaryAppended children first singleton second suffix middle jobs
    hchildren ht hm hj
  have hfirst := OriginalAllPositionContextDeleteBaseProof.lookupZero jobs first middle hrow
  have hsecond := OriginalAllPositionContextDeleteBaseProof.lookupZero middle second suffix hm
  have hiff := OriginalAllPositionContextDeleteDropProof.lookupConsIff jobs first middle z second hrow
  obtain ⟨hiff⟩ := hiff
  obtain ⟨hsecond⟩ := hsecond
  exact andIntro hfirst ⟨Derivation.implicationElimination (Derivation.conjunctionRight hiff) hsecond⟩

theorem rows (raw parameter jobs first second children suffix : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs children raw parameter)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs children suffix))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup first z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup second (numeral 1) jobs))) := by
  let qs : Fin 2 → Program 2 := ![OriginalHereditaryExpansion.consOf (.projection 0) (OriginalRawSyntaxTransport.constant 2 0),
    OriginalHereditaryExpansion.consOf (.projection 0) (.projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons second (Fin.cons suffix Fin.elim0)
  apply queryCases qs xs _
  intro beta rho ys Theta hinc hq
  simp only [conjunctionRename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  let xx : Fin 2 → OTerm beta := Fin.cons (second.relabel rho) (Fin.cons (suffix.relabel rho) Fin.elim0)
  have hx : (fun i => (xs i).relabel rho) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hx] at hq
  have ha' := renameInto ha rho Theta hinc
  have hf' := renameInto hf rho Theta hinc
  have hs' := renameInto hs rho Theta hinc
  have hc' := renameInto hc rho Theta hinc
  have hj' := renameInto hj rho Theta hinc
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ha' hf' hs' hc' hj'
  have ht := binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
    (ys 0) (second.relabel rho) z xx (hq 0) (projectionValue 0 xx) (constantValue 0 xx)
  have hm := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 1) (second.relabel rho) (suffix.relabel rho) xx (hq 1) (projectionValue 0 xx) (projectionValue 1 xx)
  exact atRows (raw.relabel rho) (parameter.relabel rho) (jobs.relabel rho)
    (first.relabel rho) (second.relabel rho) (children.relabel rho) (suffix.relabel rho) (ys 0) (ys 1)
    ha' hf' hs' hc' hj' ht hm

theorem actual (raw parameter jobs first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup first z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup second (numeral 1) jobs))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply programCompositionCases InternalApplicationValidityStackAppend.append
    ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs _ he
  intro beta rho ys Theta hinc happ hq
  simp only [conjunctionRename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
  have hx : (fun i => (xs i).relabel rho) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hx] at hq
  have hy : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have ha' := renameInto ha rho Theta hinc
  have hf' := renameInto hf rho Theta hinc
  have hs' := renameInto hs rho Theta hinc
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ha' hf' hs'
  exact rows (raw.relabel rho) (parameter.relabel rho) (jobs.relabel rho)
    (first.relabel rho) (second.relabel rho) (ys 0) (ys 1) ha' hf' hs' (hq 0)
    (by simpa only [graph2,hy] using happ)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildRawLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildRawLookupProof
