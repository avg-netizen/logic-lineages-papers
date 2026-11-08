module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftRepresentativeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRepresentativeApplicationCongruenceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- A proof-local side selector; both branches are the original selected
representative programs, and no new representative is chosen. -/
def representative (sourceSide : Bool) (data : Data) : Program 1 :=
  if sourceSide then (InternalCertifiedSourceGuardSelection.edgeData data).sourceRepresentative
  else (InternalCertifiedSourceGuardSelection.edgeData data).targetRepresentative

theorem representativeAtPayloads (sourceSide : Bool) (data : Data)
    (arrow d e f a parent x out fp ap : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hvf : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.validity data).sourceValid InternalOriginalStepGuard.one f)))
    (hvp : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hhf : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.goodRun data) InternalOriginalStepGuard.one f)))
    (hha : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.goodRun data) InternalOriginalStepGuard.one a)))
    (hna : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.normalizer data) a a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hc : Nonempty (Derivation body Gamma
      (graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge) out d e x a)))
    (hr : Nonempty (Derivation body Gamma (graph1 (representative sourceSide data) x f))) :
    Nonempty (Derivation body Gamma (graph1 (representative sourceSide data) out parent)) := by
  have h : Nonempty (Derivation body Gamma
      (InternalRepresentativeApplicationCongruence.applicationPremises
        data.oldValidity data.member data.oldEdge arrow d e fp ap f a parent x out)) :=
    andIntro (andIntro har (andIntro (reconstructPair f arrow fp hfl hfp)
      (andIntro (reconstructPair a d ap hal hap)
        (applicationForward d e f a fp ap parent hfp hap hp))))
      (andIntro hvf (andIntro hhf (andIntro hha (andIntro hna (andIntro hvp hc)))))
  cases sourceSide with
  | false =>
      exact andRight (InternalRepresentativeApplicationCongruenceApplicationProof.targetApplication
        data.oldValidity data.member data.oldEdge arrow d e fp ap f a parent x out hr h)
  | true =>
      exact andRight (InternalRepresentativeApplicationCongruenceApplicationProof.sourceApplication
        data.oldValidity data.member data.oldEdge arrow d e fp ap f a parent x out hr h)

/-- The original right-selector witnesses are obtained and eliminated
internally, leaving only raw application and the derived raw tag graphs. -/
theorem rawRepresentativeApplication (sourceSide : Bool) (data : Data)
    (arrow d e f a parent x out : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hvf : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.validity data).sourceValid InternalOriginalStepGuard.one f)))
    (hvp : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hhf : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.goodRun data) InternalOriginalStepGuard.one f)))
    (hha : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.goodRun data) InternalOriginalStepGuard.one a)))
    (hna : Nonempty (Derivation body Gamma
      (graph1 (InternalCertifiedSourceGuardSelection.normalizer data) a a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hc : Nonempty (Derivation body Gamma
      (graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge) out d e x a)))
    (hr : Nonempty (Derivation body Gamma (graph1 (representative sourceSide data) x f))) :
    Nonempty (Derivation body Gamma (graph1 (representative sourceSide data) out parent)) := by
  apply queryCases ![rightOf (.projection (0 : Fin 2)),rightOf (.projection (1 : Fin 2))]
    (Fin.cons f (Fin.cons a Fin.elim0)) _
  intro β j ys Delta hj hq
  rw [graph1Rename]
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hvf' := renameInto hvf j Delta hj
  have hvp' := renameInto hvp j Delta hj
  have hhf' := renameInto hhf j Delta hj
  have hha' := renameInto hha j Delta hj
  have hna' := renameInto hna j Delta hj
  have hp' := renameInto hp j Delta hj
  have hc' := renameInto hc j Delta hj
  have hr' := renameInto hr j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,oneRename]
    at har' hfl' hal' hvf' hvp' hhf' hha' hna' hp' hc' hr'
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 2 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfp := InternalOriginalTypedCarrierSupportProof.atRecover InternalUnpair.right
    (0 : Fin 2) (ys 0) xs (hq 0)
  have hap := InternalOriginalTypedCarrierSupportProof.atRecover InternalUnpair.right
    (1 : Fin 2) (ys 1) xs (hq 1)
  exact representativeAtPayloads sourceSide data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (parent.relabel j) (x.relabel j) (out.relabel j) (ys 0) (ys 1)
    har' hfl' hal' hfp hap hvf' hvp' hhf' hha' hna' hp' hc' hr'

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftRepresentativeProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftRepresentativeProof
