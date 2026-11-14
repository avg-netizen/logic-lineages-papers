module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroValue (E : Program 3) (pool reached parameter : OTerm alpha) :
    Nonempty (Derivation body Delta (graph4 (iterate E) reached z pool reached parameter)) :=
  recursionZeroValue (.projection 1)
    (.composition (PrimaryExpansion.expand E) ![.projection 2,.projection 1,.projection 4])
    reached ![pool,reached,parameter] (projectionValue 1 ![pool,reached,parameter])

theorem successorValue (E : Program 3) (count previous out pool reached parameter : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph4 (iterate E) previous count pool reached parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) out pool previous parameter))) :
    Nonempty (Derivation body Delta (graph4 (iterate E) out (suc count) pool reached parameter)) := by
  let step : Program 5 := .composition (PrimaryExpansion.expand E) ![.projection 2,.projection 1,.projection 4]
  have hs : Nonempty (Derivation body Delta (programGraph step out ![count,previous,pool,reached,parameter])) := by
    apply compositionValue (PrimaryExpansion.expand E) ![.projection 2,.projection 1,.projection 4]
      out ![count,previous,pool,reached,parameter] ![pool,previous,parameter] he
    intro i
    exact Fin.cases (projectionValue 2 _) (Fin.cases (projectionValue 1 _)
      (Fin.cases (projectionValue 4 _) (fun k => Fin.elim0 k))) i
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction
    Delta (OrdinaryArithmetic.graphFormula (.projection (1 : Fin 3)))
    (OrdinaryArithmetic.graphFormula step) out count previous ![pool,reached,parameter] hr hs

theorem successorRecover (E : Program 3) (count previous out pool reached parameter : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph4 (iterate E) previous count pool reached parameter)))
    (ho : Nonempty (Derivation body Delta (graph4 (iterate E) out (suc count) pool reached parameter))) :
    Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) out pool previous parameter)) := by
  apply programCases (PrimaryExpansion.expand E) (Fin.cons pool (Fin.cons previous (Fin.cons parameter Fin.elim0))) _
  intro beta j Theta value hj hv
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hv
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have ho' := renameInto ho j Theta hj
  simp only [graph4Rename,sucRelabel] at ho'
  have hn := successorValue E (count.relabel j) (previous.relabel j) value
    (pool.relabel j) (reached.relabel j) (parameter.relabel j) hr' hv
  have hu := valueUnique (iterate E) value (out.relabel j)
    ![suc (count.relabel j),pool.relabel j,reached.relabel j,parameter.relabel j] hn ho'
  exact outputTransport (PrimaryExpansion.expand E) value (out.relabel j)
    ![pool.relabel j,previous.relabel j,parameter.relabel j] hu hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
