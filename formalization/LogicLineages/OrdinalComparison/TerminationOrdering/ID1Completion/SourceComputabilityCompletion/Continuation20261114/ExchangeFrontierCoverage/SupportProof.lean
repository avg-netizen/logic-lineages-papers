module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open RawHeadWindowCoverage.RelationFoldCoreProof
open GuardedSourceSyntaxProof (numeralRename)

theorem paramsOne (params : Fin 1 → OTerm alpha) : params = Fin.cons (params 0) Fin.elim0 := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem observe (D : Program 2) (node param deps child : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (graph3 (dependencyMember D) (numeral 1) child node param)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons child (Fin.cons node (Fin.cons param Fin.elim0))
  have hg := binaryValue D (.projection 1) (.projection 2) deps node param xs hd
    (projectionValue 1 xs) (projectionValue 2 xs)
  exact binaryValue contains (.composition D ![.projection 1,.projection 2]) (.projection 0)
    (numeral 1) deps child xs hm hg (projectionValue 0 xs)

theorem hitAt (D : Program 2) (head rest out image param deps : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps head param)))
    (ht : Nonempty (Derivation body Delta (graph3 (dependencyMember D) (numeral 1) image head param)))
    (hs : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.flattenStep D) out head rest param))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image)) := by
  let ys : Fin 3 → OTerm alpha := Fin.cons image (Fin.cons head (Fin.cons param Fin.elim0))
  have hy := binaryValue D (.projection 1) (.projection 2) deps head param ys hd
    (projectionValue 1 ys) (projectionValue 2 ys)
  have hm := binaryRecover contains (.composition D ![.projection 1,.projection 2]) (.projection 0)
    (numeral 1) deps image ys ht hy (projectionValue 0 ys)
  let xs : Fin 3 → OTerm alpha := Fin.cons head (Fin.cons rest (Fin.cons param Fin.elim0))
  have hx := binaryValue D (.projection 0) (.projection 2) deps head param xs hd
    (projectionValue 0 xs) (projectionValue 2 xs)
  exact RawHeadWindowCoverage.SupportProof.appendLeft (.composition D ![.projection 0,.projection 2])
    (.projection 1) out deps image xs hx hm hs

theorem hit (D : Program 2) : Hit body (ExchangeFrontier.flattenStep D) (dependencyMember D) := by
  intro alpha Delta head rest out image params ht hs
  rw [paramsOne params] at ht hs
  apply programCases D (Fin.cons head (Fin.cons (params 0) Fin.elim0)) _
  intro beta j Theta deps hj hd
  simp only [graph2Rename,numeralRename]
  simp only [consTermRename,emptyRename] at hd
  have htj := renameInto ht j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [programRename,consTermRename,emptyRename,numeralRename] at htj hsj
  exact hitAt D (head.relabel j) (rest.relabel j) (out.relabel j) (image.relabel j)
    ((params 0).relabel j) deps hd htj hsj

theorem keep (D : Program 2) : Tail body (ExchangeFrontier.flattenStep D) := by
  intro alpha Delta head rest out image params hm hs
  exact RawHeadWindowCoverage.SupportProof.appendRight (.composition D ![.projection 0,.projection 2])
    (.projection 1) out rest image (Fin.cons head (Fin.cons rest params))
    (projectionValue 1 (Fin.cons head (Fin.cons rest params))) hm hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.SupportProof
