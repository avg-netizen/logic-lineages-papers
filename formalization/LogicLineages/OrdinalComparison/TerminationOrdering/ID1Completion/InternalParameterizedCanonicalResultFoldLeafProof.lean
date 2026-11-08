module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalParameterizedCanonicalResultFoldBindingProof InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem descentInvariant (data : Data) (out input typ parameter : OTerm α)
    (hd : Nonempty (Derivation body Gamma (graph2 (leaf data) out input parameter)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data out typ parameter)) :=
  InternalOriginalUniformDescentSelectionInternalProof.descentInvariant
    data.oldRepresentative (validity data) out input typ parameter (andIntro hd hs)

theorem leafHasOutput (data : Data) (input typ parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard data))
        z input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  apply programCases (leaf data) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta out hj hd
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hd
  have hs' := renameInto hs j Delta hj
  rw [sourcePremisesRename] at hs'
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  have hc := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (rootGuard data) (leaf data) (combine data)
    (input.relabel j) out (parameter.relabel j) hg' hd
  exact hasCertifiedOutputIntro data out (input.relabel j) (typ.relabel j) (parameter.relabel j)
    (andIntro hc (descentInvariant data out (input.relabel j) (typ.relabel j)
      (parameter.relabel j) hd hs'))

theorem certifiedTagTransport (data : Data) (out input typ other parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn typ other)))
    (h : Nonempty (Derivation body Gamma (certifiedOutput data out input typ parameter))) :
    Nonempty (Derivation body Gamma (certifiedOutput data out input other parameter)) := by
  have hi := andRight h
  exact andIntro (andLeft h) (andIntro (andLeft hi)
    (andIntro (outputTransport InternalUnpair.left typ other (Fin.cons out Fin.elim0)
      he (andLeft (andRight hi))) (andRight (andRight hi))))

theorem hasOutputTagTransport (data : Data) (input typ other parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn typ other)))
    (h : Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input other parameter)) := by
  apply hasCertifiedOutputCases data input typ parameter _ h
  intro β j Delta out hj hc
  rw [hasCertifiedOutputRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact hasCertifiedOutputIntro data out (input.relabel j) (other.relabel j) (parameter.relabel j)
    (certifiedTagTransport data out (input.relabel j) (typ.relabel j) (other.relabel j)
      (parameter.relabel j) he' hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldLeafProof
