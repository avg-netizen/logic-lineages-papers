module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineQueriesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableObject OriginalVariableObjectSyntaxProof OriginalVariableObjectCertificateCoreProof
open InternalComputabilityApplication InternalAccessibilityRules
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalComputabilityDownwardSyntaxProof (typedRename certificateRename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (OTerm)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original coordinate programs bind the shared Gamma, both payloads
and parameter internally. The final antecedent contains only original
typedness, the read-only variable test, and the original source certificate. -/
theorem certificateBottom (p : GlobalSourcePackage.Inputs) (context : Nat)
    (hw : evaluate p.window (List.Vector.ofFn ![context]) = 1)
    (tau : Ty) (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (source target witness : OTerm α)
    (ht : Nonempty (Derivation body Delta
      (typed (GlobalSourcePackage.computability (OriginalVariableRepresentative.refineInputs p))
        tau (numeral context) source)))
    (hv : Nonempty (Derivation body Delta (variableObject source)))
    (hc : Nonempty (Derivation body Delta
      (certificate (GlobalSourcePackage.source (OriginalVariableRepresentative.refineInputs p))
        false context source target witness))) :
    Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target)) := by
  apply GlobalSourceSpineQueriesProof.coordinateCases BottomSpineMeasure.measure
    (numeral context) source target _
  intro β j Theta gammaCode x y parameter _mark _depth hj hg hx hy hp _hm _hd
  rw [bottomAtSourceGammaRename]
  have ht' := renameInto ht j Theta hj
  simp only [typedRename,numeralRename] at ht'
  have hv' := renameInto hv j Theta hj
  rw [variableObjectRename] at hv'
  have hc' := renameInto hc j Theta hj
  rw [certificateRename] at hc'
  simp only [numeralRename] at hp
  have hwindow := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Theta) (α := β) p.window context hw
  exact certificateAtCoordinates p context tau (source.relabel j) (target.relabel j)
    (witness.relabel j) gammaCode x y parameter hwindow hg hx hy hp ht' hv' hc'

theorem actualOriginalVariableObjectCertificateBottom :
    OriginalVariableObjectTargets.ActualOriginalVariableObjectCertificateBottom := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS tau α Delta source target witness
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := GlobalSourcePackage.source (OriginalVariableRepresentative.refineInputs p)
  let comp := GlobalSourcePackage.computability (OriginalVariableRepresentative.refineInputs p)
  let H := typed comp tau (numeral context) source ⊓
    (variableObject source ⊓ certificate src false context source target witness)
  have hh : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Delta) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := OuterWindowProof.closedWindowEvaluation n p.window hp.2.1 symbols S table hS
  obtain ⟨result⟩ := certificateBottom p context hw tau (SourcePresentation.sourceBody src context)
    α (H :: Delta) source target witness (andLeft hh) (andLeft (andRight hh)) (andRight (andRight hh))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateProof
