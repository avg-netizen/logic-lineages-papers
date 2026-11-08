module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection InternalOriginalUniformDescentSelectionTargets
open InternalParameterizedApplicationValidityFold InternalApplicationValidityClosure
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Both actual binary validators close at the same original parameter.
Target validity uses its existing constant-one node, while universe validity
uses the supplied actual codomain-membership graph. -/
theorem sourceApplicationClosure (data : Data)
    (arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hm : Nonempty (Derivation body Gamma
      (graph2 data.member (suc z) e parameter)))
    (hf : Nonempty (Derivation body Gamma
      (graph2 (validity data) (suc z) fn parameter)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 (validity data) (suc z) arg parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (validity data) (suc z) parent parameter)) := by
  have hfs := conjunctionRecover (targetP data.oldTarget) (universeP data.oldSource data.member)
    (Fin.cons fn (Fin.cons parameter Fin.elim0)) hf
  have has := conjunctionRecover (targetP data.oldTarget) (universeP data.oldSource data.member)
    (Fin.cons arg (Fin.cons parameter Fin.elim0)) ha
  have htarget := andIntro hc
    (andIntro (InternalLessThanSupportProof.oneConstantValue
      (Fin.cons e (Fin.cons parameter Fin.elim0))) (andIntro (andLeft hfs) (andLeft has)))
  have huniverse := andIntro hc (andIntro hm (andIntro (andRight hfs) (andRight has)))
  obtain ⟨ht⟩ :=
    InternalParameterizedApplicationValidityFoldInternalProof.actualOriginalParameterizedValidityFoldApplicationClosure
      body (InternalLessThan.constantOne 2) data.oldTarget α Gamma
      arrow d e fp ap fn arg parent parameter
  obtain ⟨hu⟩ :=
    InternalParameterizedApplicationValidityFoldInternalProof.actualOriginalParameterizedValidityFoldApplicationClosure
      body data.member data.oldSource α Gamma arrow d e fp ap fn arg parent parameter
  obtain ⟨htarget⟩ := htarget
  obtain ⟨huniverse⟩ := huniverse
  exact conjunctionAccept (targetP data.oldTarget) (universeP data.oldSource data.member)
    (Fin.cons parent (Fin.cons parameter Fin.elim0))
    ⟨Derivation.implicationElimination ht htarget⟩
    ⟨Derivation.implicationElimination hu huniverse⟩

theorem actualParameterizedSourceApplicationClosure : ActualParameterizedSourceApplicationClosure := by
  intro body data α Gamma arrow d e fp ap fn arg parent parameter
  let P := applicationPremises data arrow d e fp ap fn arg parent parameter
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := sourceApplicationClosure data arrow d e fp ap fn arg parent parameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andRight (andRight (andRight hp)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionApplicationProof
