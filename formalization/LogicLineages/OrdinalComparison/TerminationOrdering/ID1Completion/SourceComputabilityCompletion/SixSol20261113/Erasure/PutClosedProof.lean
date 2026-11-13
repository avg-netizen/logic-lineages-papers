module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutClosedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem closed (endpoint : Program 6) (window : Program 1) (leaf : Program 4)
    (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s)))
    (hl : Nonempty (Derivation body Delta (graph4 leaf (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window leaf) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  let inner := OriginalHereditaryLambdaGlobal.wrapper endpoint window leaf
  have hs : Nonempty (Derivation body Delta
      (graph4 OriginalHereditaryLambda.stop (suc z) s t cert parameter)) :=
    zeroBranchIntro _ _ _ (suc z) xs
      (normalizeReject OriginalLambdaGuardLeaf.sourceLambda xs
        (PutWrapperGuardsProof.zeroNotOne _ xs (PutWrapperGuardsProof.lambdaZero s t cert parameter ht)))
      (InternalLessThanSupportProof.oneConstantValue xs)
  have hg := OriginalHereditaryLambdaStoppedProof.stoppedGuard inner body alpha Delta s t cert parameter hs
  have hi := PutWrapperGuardsProof.wrapper endpoint window leaf s t cert parameter ht hl
  exact PutWrapperGuardsProof.wrapper endpoint window (OriginalHereditaryLambda.refined inner)
    s t cert parameter ht (conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hi hg)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutClosedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutClosedProof
