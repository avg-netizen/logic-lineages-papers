module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathBottomOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableQuotientPath OriginalVariableQuotientPathBottomOpeningProof
open OriginalVariableRepresentative (windowGraph)
open BottomRepresentative
open InternalParameterizedCanonicalResultFold
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof
open InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Internal contradiction in each direction, without reflecting a Delta
proof into a metalevel fact. -/
theorem rejectedIff (P Q : Formula α)
    (hp : Nonempty (Derivation body Gamma P.not))
    (hq : Nonempty (Derivation body Gamma Q.not)) :
    Nonempty (Derivation body Gamma (P.iff Q)) := by
  obtain ⟨hp'⟩ := withHyp hp P
  obtain ⟨hq'⟩ := withHyp hq Q
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction
      (Derivation.explosion (Derivation.implicationElimination hp'
        (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction
      (Derivation.explosion (Derivation.implicationElimination hq'
        (Derivation.hypothesis List.mem_cons_self))))⟩

/-- Closed roots inherit the selected representative's exact bottom test.
Open roots and their rebuilt application outputs are both not bottom. -/
theorem fullFoldBottomPreservation (data : Data) (window : Program 1) :
    FullFoldBottomPreservation (readyData data window) window := by
  intro body α Delta out input typeCode parameter
  let selected := readyData data window
  let A := windowGraph window input parameter ⊓
    (sourcePremises selected input typeCode parameter ⊓ foldGraph selected out input parameter)
  have hA : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft hA
  have hv := andLeft (andLeft (andRight hA))
  have hn := andRight (andRight hA)
  have hresult : Nonempty (Derivation body (A :: Delta)
      ((bottomAccepted out).iff (bottomAccepted input))) := by
    let P := graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected))
      (suc z) input parameter
    apply formulaCases P
    · have hp : Nonempty (Derivation body (P :: A :: Delta) P) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hnot := openingNonBottom data window out input parameter
        (withHyp hw P) (withHyp hn P) hp
      exact rejectedIff (bottomAccepted out) (bottomAccepted input)
        (andLeft hnot) (andRight hnot)
    · have hz : Nonempty (Derivation body (P.not :: A :: Delta)
          (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected))
            z input parameter)) :=
        InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
          (Fin.cons input (Fin.cons parameter Fin.elim0))
          (show Nonempty (Derivation body (P.not :: A :: Delta) P.not) from
            ⟨Derivation.hypothesis List.mem_cons_self⟩)
      have hl := OriginalVariableRepresentativeRigidityProof.closedLeafGraph selected
        out input parameter hz (withHyp hn P.not)
      exact selectedBottomIff data window out input parameter
        (withHyp hw P.not) (withHyp hv P.not) hl
  obtain ⟨hresult⟩ := hresult
  exact ⟨Derivation.implicationIntroduction hresult⟩

/-- Literal original pipeline identity; no additional Data normalization. -/
theorem outerData (data : Data) (window : Program 1) :
    UniformCertificateCompletion.OuterSelection.data data window =
      readyData (SpineApplicationTargets.parameters data window) window := rfl

theorem actualOriginalFullFoldBottomPreservation :
    OriginalVariableQuotientPathTargets.ActualOriginalFullFoldBottomPreservation := by
  intro p
  let r := OriginalVariableRepresentative.refineInputs p
  change FullFoldBottomPreservation
    (UniformCertificateCompletion.OuterSelection.data r.base r.window) r.window
  rw [outerData]
  exact fullFoldBottomPreservation (SpineApplicationTargets.parameters r.base r.window) r.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathBottomProof
