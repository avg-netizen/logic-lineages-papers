module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem iffRename {beta : Type} (P Q : Formula alpha) (j : alpha → beta) :
    (P.iff Q).relabel j = (P.relabel j).iff (Q.relabel j) := rfl

/-- Only projection wiring; its graph recovery does not assume native values. -/
theorem wireRecover {m n : Nat} (p : Program n) (indices : Fin n → Fin m)
    (out : OTerm alpha) (xs : Fin m → OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (programGraph (.composition p (fun i => .projection (indices i))) out xs))) :
    Nonempty (Derivation body Delta (programGraph p out (fun i => xs (indices i)))) :=
  compositionRecover p (fun i => .projection (indices i)) out xs
    (fun i => xs (indices i)) h (fun i => projectionValue (indices i) xs)

/-- All extra values are outputs of total original Programs, selected once
from the unchanged arguments. -/
def queries : Fin 6 → Program 14 := ![
  .composition OriginalLambdaConstructor.arrow ![.projection 8,.projection 9],
  leftOf (.projection 6),rightOf (.projection 6),
  consOf (InternalAcceptance.constantZero 14) (leftOf (.projection 6)),
  .composition OriginalHereditaryLambda.live ![.projection 0,.projection 1,.projection 2,.projection 3],
  .composition OriginalHereditaryLambda.live ![.projection 4,.projection 5,.projection 6,.projection 7] ]

theorem hop (source : Program 2) (oldStep : Program 4)
    (s t cert parameter childS childT childCert childParam d e context gamma extended out : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended))) :
    Nonempty (Derivation body Delta
      ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
        (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert childParam))) := by
  let xs : Fin 14 → OTerm alpha := ![s,t,cert,parameter,childS,childT,childCert,childParam,d,e,context,gamma,extended,out]
  apply queryCases queries xs _
  intro beta j ys Gamma hj hq
  have h' := renameInto h j Gamma hj
  simp only [LambdaHop,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at h'
  let xx : Fin 14 → OTerm beta := fun i => (xs i).relabel j
  have harrow := binaryRecover OriginalLambdaConstructor.arrow (.projection 8) (.projection 9)
    (ys 0) (d.relabel j) (e.relabel j) xx (hq 0) (projectionValue 8 xx) (projectionValue 9 xx)
  have hleft := unaryRecover InternalUnpair.left (.projection (6 : Fin 14))
    (ys 1) (childCert.relabel j) xx (hq 1) (projectionValue 6 xx)
  have hright := unaryRecover InternalUnpair.right (.projection (6 : Fin 14))
    (ys 2) (childCert.relabel j) xx (hq 2) (projectionValue 6 xx)
  have hcons := binaryRecover InternalListCodec.consCode (InternalAcceptance.constantZero 14)
    (leftOf (.projection 6)) (ys 3) z (ys 1) xx (hq 3) (constantZeroValue xx) (hq 1)
  have hstate := wireRecover OriginalHereditaryLambda.live (![0,1,2,3] : Fin 4 → Fin 14)
    (ys 4) xx (hq 4)
  have hnext := wireRecover OriginalHereditaryLambda.live (![4,5,6,7] : Fin 4 → Fin 14)
    (ys 5) xx (hq 5)
  have hparentWire : (fun i => xx ((![0,1,2,3] : Fin 4 → Fin 14) i)) =
      ![s.relabel j,t.relabel j,cert.relabel j,parameter.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
  have hchildWire : (fun i => xx ((![4,5,6,7] : Fin 4 → Fin 14) i)) =
      ![childS.relabel j,childT.relabel j,childCert.relabel j,childParam.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
  rw [hparentWire] at hstate
  rw [hchildWire] at hnext
  have hout := OriginalTransparentMixedPathLambdaPrefixCoreProof.atWitnesses source oldStep
    (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
    (childS.relabel j) (childT.relabel j) (childCert.relabel j) (childParam.relabel j)
    (d.relabel j) (e.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j)
    (out.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    h' harrow hleft hright hcons hstate hnext
  simpa only [iffRename,graph4Rename] using hout

theorem actualLambdaPrefix :
    OriginalTransparentMixedPathLambdaPrefixTargets.ActualLambdaPrefix := by
  intro source oldStep body alpha Delta s t cert parameter childS childT childCert childParam d e context gamma extended out
  let A := LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended
  obtain ⟨hout⟩ := hop source oldStep s t cert parameter childS childT childCert childParam d e context gamma extended out
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
