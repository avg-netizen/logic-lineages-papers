module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryRawLookupProof
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

theorem rows (raw parameter jobs first children suffix : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs children raw parameter)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs children suffix))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z jobs)) := by
  have hchildren := OriginalHereditaryInternalExpansionChildrenProof.unaryCons
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) children first ha hc hf
  have hrow := OriginalHereditaryInternalFinitePrefixAppendProof.unaryAppended children first suffix jobs hchildren hj
  exact OriginalAllPositionContextDeleteBaseProof.lookupZero jobs first suffix hrow

theorem actual (raw parameter jobs first : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z jobs)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply programCompositionCases InternalApplicationValidityStackAppend.append
    ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs _ he
  intro beta rho ys Theta hinc happ hq
  simp only [graph2Rename,zRelabel]
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
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ha' hf'
  exact rows (raw.relabel rho) (parameter.relabel rho) (jobs.relabel rho)
    (first.relabel rho) (ys 0) (ys 1) ha' hf' (hq 0)
    (by simpa only [graph2,hy] using happ)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryRawLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryRawLookupProof
