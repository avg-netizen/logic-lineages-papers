module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasure sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedAuxMeasureProof (exact_OpenCoverSharedAuxMeasureParent)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Re-export of the accepted auxiliary-term rename, so later modules need not
import its heavy home module. -/
theorem auxiliaryTermRename {β : Type} (dom cod fn arg : OTerm α) (j : α → β) :
    (auxiliaryTerm dom cod fn arg).relabel j =
      auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) :=
  auxiliaryRename dom cod fn arg j

private theorem pairInputsTransport (p : Program 2) (out x y x' y' : OTerm α)
    (hx : Nonempty (Derivation body Γ (eqn x x')))
    (hy : Nonempty (Derivation body Γ (eqn y y')))
    (h : Nonempty (Derivation body Γ (programGraph p out ![x,y]))) :
    Nonempty (Derivation body Γ (programGraph p out ![x',y'])) := by
  apply graphInputTransport body α 2 Γ (OrdinaryArithmetic.graphFormula p) out ![x,y] ![x',y'] _ h
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [onEquality]
    exact hx
  · obtain rfl := Fin.eq_zero k
    rw [onEquality]
    exact hy

attribute [local irreducible] programGraph

/-- One parent measure, a known function measure and a known argument measure
pin the combiner output at exactly those two inputs. -/
private theorem combineAt (M : Program 1) (dom cod fn arg x m ma0 : OTerm α)
    (px : Nonempty (Derivation body Γ (unary (sharedMeasure M) x (auxiliaryTerm dom cod fn arg))))
    (cf : Nonempty (Derivation body Γ (unary (sharedMeasure M) m fn)))
    (ca : Nonempty (Derivation body Γ (unary (sharedMeasure M) ma0 arg))) :
    Nonempty (Derivation body Γ (programGraph chosenCombine x ![m,ma0])) := by
  apply exact_OpenCoverSharedAuxMeasureParent M body α Γ dom cod fn arg x _ px
  intro β j Δ old mf ma df da bf ba keep row
  rw [programRename,binaryInputsRename]
  have cf' := renameInto cf j Δ keep
  have ca' := renameInto ca j Δ keep
  rw [unaryRename] at cf' ca'
  have eF : Nonempty (Derivation body Δ (eqn mf (m.relabel j))) :=
    valueUnique (selectedMeasure (sharedMeasureUpdate M)) mf (m.relabel j) ![fn.relabel j]
      row.fnData.selected cf'
  have eA : Nonempty (Derivation body Δ (eqn ma (ma0.relabel j))) :=
    valueUnique (selectedMeasure (sharedMeasureUpdate M)) ma (ma0.relabel j) ![arg.relabel j]
      row.argData.selected ca'
  exact pairInputsTransport chosenCombine (x.relabel j) mf ma (m.relabel j) (ma0.relabel j)
    eF eA row.combined

theorem exact_OpenSharedAuxMeasureEquality : ExactOpenSharedAuxMeasureEquality := by
  intro M body α Γ dom cod fn fn' arg m x y cf cg px py
  apply programCases (sharedMeasure M) ![arg] (eqn x y)
  intro β j Δ ma0 keep ca
  rw [inputsRename] at ca
  rw [eqnRelabel]
  have cf' := renameInto cf j Δ keep
  have cg' := renameInto cg j Δ keep
  have px' := renameInto px j Δ keep
  have py' := renameInto py j Δ keep
  rw [unaryRename] at cf' cg' px' py'
  rw [auxiliaryRename] at px'
  rw [auxiliaryRename] at py'
  have hx := combineAt M _ _ _ _ (x.relabel j) (m.relabel j) ma0 px' cf' ca
  have hy := combineAt M _ _ _ _ (y.relabel j) (m.relabel j) ma0 py' cg' ca
  exact valueUnique chosenCombine (x.relabel j) (y.relabel j) ![m.relabel j,ma0] hx hy

/-- A held parent measure at one function moves to the other function with the
same function measure; the measure at the second parent comes from totality. -/
private theorem transfer (M : Program 1) (dom cod fn fn' arg m p : OTerm α)
    (cf : Nonempty (Derivation body Γ (unary (sharedMeasure M) m fn)))
    (cg : Nonempty (Derivation body Γ (unary (sharedMeasure M) m fn')))
    (pa : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn' arg))) := by
  apply programCases (sharedMeasure M) ![auxiliaryTerm dom cod fn' arg] _
  intro β j Δ q keep qb
  rw [inputsRename,auxiliaryRename] at qb
  rw [unaryRename,auxiliaryRename]
  have cf' := renameInto cf j Δ keep
  have cg' := renameInto cg j Δ keep
  have pa' := renameInto pa j Δ keep
  rw [unaryRename] at cf' cg' pa'
  rw [auxiliaryRename] at pa'
  obtain ⟨e⟩ := exact_OpenSharedAuxMeasureEquality M body β Δ _ _ _ _ _ (m.relabel j) (p.relabel j) q
    cf' cg' pa' qb
  exact outputTransport (sharedMeasure M) q (p.relabel j) _ ⟨symm e⟩ qb

theorem exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent :
    ExactOpenCoverCombinedRestrictedPairedSharedMeasureParent := by
  intro V TV M M0 B T s body α Γ dom cod f g arg m goal P a b cf cg k
  apply programCases (selectedMeasure P.R) ![a] goal
  intro β j Δ p keep pa
  rw [inputsRename] at pa
  have cf' := renameInto cf j Δ keep
  have cg' := renameInto cg j Δ keep
  rw [unaryRename] at cf' cg'
  have pa' : Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) (f.relabel j) (arg.relabel j)))) := by
    rw [← auxiliaryRename]
    exact pa
  have pb' := transfer _ (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j)
    (m.relabel j) p cf' cg' pa'
  have pb : Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p (b.relabel j))) := by
    show Nonempty (Derivation body Δ
      (unary (selectedMeasure P.R) p ((auxiliaryTerm dom cod g arg).relabel j)))
    rw [auxiliaryRename]
    exact pb'
  exact k β j Δ p keep pa pb

#print axioms exact_OpenSharedAuxMeasureEquality
#print axioms exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
