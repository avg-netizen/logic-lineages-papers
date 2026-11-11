module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaGuardLeaf OriginalLambdaGuardLeafInternalProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem fourTuple {X : Type} (ys : Fin 4 → X) :
    Fin.cons (ys 0) (Fin.cons (ys 1) (Fin.cons (ys 2) (Fin.cons (ys 3) Fin.elim0))) = ys := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i

/-- The original composition graph supplies its four connected intermediate
outputs simultaneously. Its outer graph is the unchanged oldStep, and the
same witnesses are passed to the continuation with all four selector graphs. -/
theorem internalChildElimination (oldStep : Program 4) :
    InternalChildElimination oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter psi ha k
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hb := recoverChildBranch oldStep source target certificate parameter ha
  apply programCompositionCases oldStep
    ![sourceBody,targetBody,childCertificate,childParameter]
    (suc z) xs psi (projectRight hb)
  intro beta j ys Theta hj ht hg
  have hm := renameInto (projectLeft hb) j Theta hj
  change Nonempty (Derivation body Theta
    ((programGraph matchingTarget (suc z) xs).relabel j)) at hm
  simp only [programRename,sucRelabel,zRelabel] at hm ht
  have hxs : (fun i => (xs i).relabel j) =
      Fin.cons (source.relabel j) (Fin.cons (target.relabel j)
        (Fin.cons (certificate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun u => Fin.elim0 u)))) i
  rw [hxs] at hm hg
  have htuple := fourTuple ys
  rw [← htuple] at ht
  exact k beta j Theta hj (ys 0) (ys 1) (ys 2) (ys 3)
    (combine hm (combine (hg 0) (combine (hg 1) (combine (hg 2) (combine (hg 3) ht)))))

theorem actualOriginalLambdaGuardLeafInternalChildElimination :
    OriginalLambdaGuardLeafTargets.ActualOriginalLambdaGuardLeafInternalChildElimination := by
  intro oldStep
  exact internalChildElimination oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalChildProof
