module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalComputabilityDownwardSyntaxProof InternalComputabilityDownwardProof
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityFormulaSupportProof
open InverseApplicationSyntaxProof (membershipRename)
open OriginalVariableObject OriginalVariableObjectSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original certificates retain the requested type. The internally bound
same-Gamma bottom graph supplies its literal spine mark, so the existing
typed-spine leastness theorem closes the successor without a type-window
membership premise or a bottom-computability oracle. -/
theorem certificateLeast (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (base : Data) (oldStep : Program 4) (window : Program 1) (oldVertex oldResult : Program 5)
    (context : Nat) (hw : evaluate window (List.Vector.ofFn ![context]) = 1) :
    let src := OuterSelection.source oldSrc oldComp base oldStep window
    let comp := OuterSelection.computability oldComp base window oldVertex oldResult
    VariableCertificateBottom src comp context →
    ∀ (tau : Ty) (α : Type) (Gamma : List (Formula α)) (f g witness : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (variableObject f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (certificate src false context f g witness)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (membership false g)) := by
  dsimp only
  intro hbottom tau α Gamma f g witness ht hv hc
  let selected := OuterSelection.data base window
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  have rules := OuterArithmeticProof.arithmeticRules oldSrc oldComp selected
    (RawScalar.checker selected) oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    window oldVertex oldResult context hw
  have htypedG := closedApply (rules.typedDown α tau f g)
    (andIntro ht (edgeIntroduction hc))
  have hb := closedApply (hbottom tau α [] f g witness)
    (andIntro ht (andIntro hv hc))
  apply OriginalVariableObjectSupportProof.bottomAtSourceGammaCases tau f g _ hb
  intro β j Delta gamma hj _ hbg
  rw [membershipRename]
  have ht' := renameInto htypedG j Delta hj
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm := GlobalSourceSpineBottomSupportProof.bottomObjectMarked tau (g.relabel j) gamma hbg
  exact GlobalSourceSpineLeastProof.least oldSrc oldComp base oldStep window oldVertex oldResult
    context hw tau β Delta (g.relabel j) (numeral (Nat.pair 1 0)) (numeral 0) ht' hm

/-- Bind the original arbitrary successor and its original existential
certificate. Variable classification is transported syntactically through
both binders, rather than replaced by a decoded source-variable premise. -/
theorem successorsFromCertificates (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (progress : ∀ (β : Type) (Delta : List (Formula β)) (x g witness : OTerm β),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (typed comp tau (numeral context) x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (variableObject x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (certificate src false context x g witness)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (membership false g)))
    (α : Type) (Gamma : List (Formula α)) (x : OTerm α)
    (ht : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) x)))
    (hv : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (variableObject x))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (successors src false context x)) := by
  let g : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let E := edge src false context (x.relabel Sum.inl) g
  let Delta := E :: Gamma.map weaken
  have hi : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have ht' := renameInto ht Sum.inl Delta hi
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hv' := renameInto hv Sum.inl Delta hi
  rw [variableObjectRename] at hv'
  have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta E) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htarget : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (membership false g)) := by
    apply edgeCases src context (x.relabel Sum.inl) g _ he
    intro β j Theta witness hj hc
    rw [membershipRename]
    have htt := renameInto ht' j Theta hj
    simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at htt
    have hvv := renameInto hv' j Theta hj
    rw [variableObjectRename] at hvv
    exact progress β Theta ((x.relabel Sum.inl).relabel j) (g.relabel j) witness htt hvv hc
  obtain ⟨htarget⟩ := htarget
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction htarget)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastSupportProof
