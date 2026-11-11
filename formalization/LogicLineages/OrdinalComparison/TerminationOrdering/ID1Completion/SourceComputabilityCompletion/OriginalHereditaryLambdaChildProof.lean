module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryLambda OriginalHereditaryLambdaChildBranchProof
open OriginalHereditaryLambdaPrefixProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open OriginalLambdaGuardLeafInternalChildProof (fourTuple)
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original composition binder creates the four actual child witnesses.
The exact original certificate-prefix graph and SAME refined acceptance are
then delivered in the continuation, without native graph reflection. -/
theorem internalChildElimination (oldStep : Program 4) :
    InternalChildElimination (refined oldStep) := by
  intro body alpha Delta source target certificate parameter psi ha k
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hb := recoverBranch oldStep xs (projectLeft ha) (projectRight ha)
  apply programCompositionCases (refined oldStep)
    ![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
      OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter]
    (suc z) xs psi (projectRight (projectRight hb))
  intro beta j ys Theta hj ht hg
  have hm := renameInto (projectLeft hb) j Theta hj
  have hp := renameInto (projectLeft (projectRight hb)) j Theta hj
  simp only [programRename,sucRelabel,zRelabel] at hm hp ht
  have hprefix := recoverPrefix (fun i => (xs i).relabel j) (ys 2) hp (hg 2)
  have hxs : (fun i => (xs i).relabel j) =
      Fin.cons (source.relabel j) (Fin.cons (target.relabel j)
        (Fin.cons (certificate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun u => Fin.elim0 u)))) i
  rw [hxs] at hm hp hg
  rw [← fourTuple ys] at ht
  exact k beta j Theta hj (ys 0) (ys 1) (ys 2) (ys 3)
    (combine hm (combine hp (combine hprefix
      (combine (hg 0) (combine (hg 1) (combine (hg 2) (combine (hg 3) ht)))))))

theorem actualOriginalHereditaryLambdaInternalChildElimination :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaInternalChildElimination := by
  intro oldStep
  exact internalChildElimination oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildProof
