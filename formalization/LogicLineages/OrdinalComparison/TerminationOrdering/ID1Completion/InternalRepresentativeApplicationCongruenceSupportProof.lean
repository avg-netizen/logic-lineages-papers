module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruencePayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalRepresentativeApplicationCongruence
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalRepresentativeApplicationCongruencePayloadProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem oneRename {β : Type} (j : α → β) :
    (InternalOriginalStepGuard.one : OTerm α).relabel j = InternalOriginalStepGuard.one := by
  simp only [InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem representationRename {β : Type} (valid p : Program 1)
    (out raw : OTerm α) (j : α → β) :
    (InternalRepresentativeTag.representation valid p out raw).relabel j =
      InternalRepresentativeTag.representation valid p (out.relabel j) (raw.relabel j) := by
  simp only [InternalRepresentativeTag.representation,conjunctionRename,graph1Rename,oneRename]

@[simp] theorem applicationPremisesRename {β : Type} (validity : InternalOriginalStepGuard.Data)
    (member : Program 1) (old : InternalQuotientEdgeChecker.Data)
    (arrow d e fp ap fn arg parent x out : OTerm α) (j : α → β) :
    (applicationPremises validity member old arrow d e fp ap fn arg parent x out).relabel j =
      applicationPremises validity member old (arrow.relabel j) (d.relabel j) (e.relabel j)
        (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
        (x.relabel j) (out.relabel j) := by
  simp only [applicationPremises,InternalApplicationValidityClosure.applicationConstructors,
    conjunctionRename,graph1Rename,graph2Rename,graph4Rename,oneRename]

/-- Source acceptance supplies target acceptance by the actual conjunction,
not by external calibration or an added implication premise. -/
theorem sourceToTarget (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (raw : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationValidityStack.recursiveData validity member).sourceValid
        InternalOriginalStepGuard.one raw))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationValidityStack.recursiveData validity member).targetValid
        InternalOriginalStepGuard.one raw)) :=
  andLeft (conjunctionRecover
    (InternalApplicationValidityStack.validator (InternalLessThan.constantOne 1) validity.targetValid)
    (InternalApplicationValidityStack.validator member validity.sourceValid)
    (Fin.cons raw Fin.elim0) h)

/-- The exact source guard opens the existing foldedData source branch. -/
theorem foldedSourceAtNormalizer (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) (out raw : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationValidityStack.recursiveData validity member).sourceValid
        InternalOriginalStepGuard.one raw)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) out raw))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalRepresentativeFoldCalibration.foldedData validity member old).sourceRepresentative
        out raw)) := by
  apply successorBranchIntro
    (InternalApplicationValidityStack.exactOne
      (InternalRepresentativeFoldCalibration.rootGuard validity member))
    (InternalAcceptance.constantZero 1)
    (InternalRepresentativeFoldCalibration.normalizer validity member old)
    out z (Fin.cons raw Fin.elim0) _ hn
  exact sameAccept (InternalRepresentativeFoldCalibration.rootGuard validity member)
    (InternalLessThan.constantOne 1) (suc z) (Fin.cons raw Fin.elim0) hv
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons raw Fin.elim0))

/-- Only the actual right payload transfers from a wrapped output x to an
actual old-program output y. No whole-output equality is asserted. -/
theorem payloadAtOutput (valid p : Program 1) (payload x raw y : OTerm α)
    (hr : Nonempty (Derivation body Gamma
      (InternalRepresentativeTag.representation valid p x raw)))
    (hp : Nonempty (Derivation body Gamma (graph1 p y raw)))
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload x))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload y)) :=
  unaryRecover InternalUnpair.right p payload y (Fin.cons raw Fin.elim0)
    (payloadBackward valid p payload x raw hr hx) hp

/-- Reintroduce a wrapper at the very same old output when its actual tag
equals the raw input's actual tag. The payload witness is eliminated inside
the calculus; no output-type invariant is assumed. -/
theorem representativeAtOutput (valid p : Program 1) (tag out raw : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 valid InternalOriginalStepGuard.one raw)))
    (hp : Nonempty (Derivation body Gamma (graph1 p out raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag raw)))
    (ho : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag out))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalRepresentativeTag.representative valid p) out raw)) := by
  apply programCases InternalUnpair.right (Fin.cons out Fin.elim0) _
  intro β j Delta payload hj hright
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hright
  have hv' := renameInto hv j Delta hj
  have hp' := renameInto hp j Delta hj
  have ht' := renameInto ht j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph1Rename,oneRename] at hv' hp' ht' ho'
  apply representativeIntro valid p (out.relabel j) (raw.relabel j) hv'
  exact binaryValue InternalPairing.pairing InternalUnpair.left (rightOf p)
    (out.relabel j) (tag.relabel j) payload (Fin.cons (raw.relabel j) Fin.elim0)
    (reconstructPair (out.relabel j) (tag.relabel j) payload ho' hright) ht'
    (unaryValue InternalUnpair.right p payload (out.relabel j)
      (Fin.cons (raw.relabel j) Fin.elim0) hright hp')

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceSupportProof
