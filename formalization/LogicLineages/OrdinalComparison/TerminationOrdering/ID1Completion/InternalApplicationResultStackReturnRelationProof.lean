module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnRelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalApplicationResultStackReturnSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem returnedRecover {n : Nat} (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (work results value : OTerm α)
    (hr : Nonempty (Derivation body Gamma (returned p out xs work results)))
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma (graph3 returnState out value work results)) := by
  apply returnedCases p out xs work results _ hr
  intro β j Delta v hj hv hret
  simp only [graph3Rename]
  have hp' := renameInto hp j Delta hj
  simp only [programRename] at hp'
  exact headTransport returnState (out.relabel j) v (value.relabel j)
    (Fin.cons (work.relabel j) (Fin.cons (results.relabel j) Fin.elim0))
    (valueUnique p v (value.relabel j) _ hv hp') hret

theorem leafResultEqReturned (leaf : Program 1) (out value work results : OTerm α) :
    leafResult leaf out value work results =
      returned leaf out (Fin.cons value Fin.elim0) work results := by
  simp only [leafResult,returned,graph1,consTermRename,emptyRename]

theorem finishResultEqReturned (combine : Program 4)
    (out d e work argument function results : OTerm α) :
    finishResult combine out d e work argument function results =
      returned combine out (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument Fin.elim0))))
        work results := by
  simp only [finishResult,returned,graph4,consTermRename,emptyRename]

@[simp] theorem leafResultRename {β : Type} (leaf : Program 1)
    (out value work results : OTerm α) (j : α → β) :
    (leafResult leaf out value work results).relabel j =
      leafResult leaf (out.relabel j) (value.relabel j) (work.relabel j) (results.relabel j) := by
  simp only [leafResultEqReturned,returnedRename,consTermRename,emptyRename]

@[simp] theorem finishResultRename {β : Type} (combine : Program 4)
    (out d e work argument function results : OTerm α) (j : α → β) :
    (finishResult combine out d e work argument function results).relabel j =
      finishResult combine (out.relabel j) (d.relabel j) (e.relabel j) (work.relabel j)
        (argument.relabel j) (function.relabel j) (results.relabel j) := by
  simp only [finishResultEqReturned,returnedRename,consTermRename,emptyRename]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnRelationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnRelationProof
