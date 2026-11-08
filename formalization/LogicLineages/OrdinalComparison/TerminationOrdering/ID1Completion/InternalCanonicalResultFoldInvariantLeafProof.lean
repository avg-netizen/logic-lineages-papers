module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph 
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldInvariantSyntaxProof
open InternalCanonicalResultFoldInvariantBindingProof InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalCanonicalDescentSelectionInternalProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The checked D laws produce the three output factors at the same witness. -/
theorem descentInvariant (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (out input typ : OTerm α)
    (hd : Nonempty (Derivation body Gamma
      (InternalCanonicalDescentSelection.representativeGraph R (validity old member) out input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ))) :
    Nonempty (Derivation body Gamma (outputInvariant old R member out typ)) :=
  andIntro (descentValidity R (validity old member) out input hd (andLeft hs))
    (andIntro (descentLeft R (validity old member) out input typ hd (andLeft hs) (andRight hs))
      (descentFixed R (validity old member) out input hd (andLeft hs)))

/-- Rejected opening follows the original D leaf, even on application-tagged
inputs. The output, actual successful run and invariant are all derived. -/
theorem leafHasOutput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (input typ : OTerm α)
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ)))
    (hg : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationResultStack.openGuard
        (InternalCanonicalResultFoldOpening.rootGuard (validity old member) member)) z input))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)) := by
  apply programCases (InternalCanonicalResultFoldOpening.leaf R (validity old member))
    (Fin.cons input Fin.elim0) _
  intro β j Delta out hj hd
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hd
  have hs' := renameInto hs j Delta hj
  rw [sourcePremisesRename] at hs'
  have hg' := renameInto hg j Delta hj
  simp only [graph1Rename,zRelabel] at hg'
  have hc := InternalApplicationCertifiedResultFoldLeafClosureProof.leafClosure
    (InternalCanonicalResultFoldOpening.rootGuard (validity old member) member)
    (InternalCanonicalResultFoldOpening.leaf R (validity old member))
    (InternalCanonicalResultFoldOpening.combine R (validity old member))
    (input.relabel j) out hg' hd
  exact hasCertifiedOutputIntro old R member out (input.relabel j) (typ.relabel j)
    (andIntro hc (descentInvariant old R member out (input.relabel j) (typ.relabel j) hd hs'))

/-- Type equality changes only the output's original left graph. -/
theorem certifiedTagTransport (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (out input typ other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn typ other)))
    (h : Nonempty (Derivation body Gamma (certifiedOutput old R member out input typ))) :
    Nonempty (Derivation body Gamma (certifiedOutput old R member out input other)) := by
  have hi := andRight h
  exact andIntro (andLeft h) (andIntro (andLeft hi)
    (andIntro (outputTransport InternalUnpair.left typ other (Fin.cons out Fin.elim0)
      he (andLeft (andRight hi))) (andRight (andRight hi))))

/-- Preserve the existential witness while transporting the requested type. -/
theorem hasOutputTagTransport (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (input typ other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn typ other)))
    (h : Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input other)) := by
  apply hasCertifiedOutputCases old R member input typ _ h
  intro β j Delta out hj hc
  rw [hasCertifiedOutputRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact hasCertifiedOutputIntro old R member out (input.relabel j) (other.relabel j)
    (certifiedTagTransport old R member out (input.relabel j) (typ.relabel j) (other.relabel j) he' hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantLeafProof
