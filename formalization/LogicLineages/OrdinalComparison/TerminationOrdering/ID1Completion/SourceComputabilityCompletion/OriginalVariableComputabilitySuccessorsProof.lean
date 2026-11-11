module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineComputableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilitySuccessorsProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalComputabilityDownwardSyntaxProof InternalComputabilityDownwardProof
open InternalComputabilityApplicationSyntaxProof
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityFormulaSupportProof
open OriginalVariableObject OriginalVariableObjectSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every ORIGINAL variable-certificate successor is typed at the requested
finite type and has the actual same-Gamma bottom mark. Typed spine C, not
an external type-window premise, proves its full computability. -/
theorem certificateComputable (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) :
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    let src := GlobalSourcePackage.source p
    let comp := GlobalSourcePackage.computability p
    VariableCertificateBottom src comp context →
    ∀ (tau : Ty) (alpha : Type) (Gamma : List (Formula alpha)) (f g witness : OTerm alpha),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (variableObject f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (certificate src false context f g witness)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computable comp tau (numeral context) g)) := by
  dsimp only
  intro hbottom tau alpha Gamma f g witness ht hv hc
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data p.base p.window
  let src := GlobalSourcePackage.source p
  let comp := GlobalSourcePackage.computability p
  have hw := GlobalSourceSpineLeastProof.windowEvaluation n p.window hp.2.1 symbols S table hS
  have rules := OuterArithmeticProof.arithmeticRules p.oldSrc p.oldComp data
    (RawScalar.checker data) p.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    p.window p.oldVertex p.oldResult context hw
  have htypedG := closedApply (rules.typedDown alpha tau f g)
    (andIntro ht (edgeIntroduction hc))
  have hb := closedApply (hbottom tau alpha [] f g witness)
    (andIntro ht (andIntro hv hc))
  apply OriginalVariableObjectSupportProof.bottomAtSourceGammaCases tau f g _ hb
  intro beta j Delta gamma hj _ hbg
  simp only [computableRename,GuardedSourceSyntaxProof.numeralRename]
  have ht' := renameInto htypedG j Delta hj
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm := GlobalSourceSpineBottomSupportProof.bottomObjectMarked tau (g.relabel j) gamma hbg
  exact GlobalSourceSpineComputableProof.computableSpine n arity p.base hp.1 p.window hp.2.1
    p.oldSrc p.oldComp p.oldStep p.oldVertex p.oldResult symbols S table hS
    tau beta Delta (g.relabel j) (numeral (Nat.pair 1 0)) (numeral 0) ht' hm

/-- Open the original existential source certificate under the actual
successor binder; no replacement relation or fixed Gamma is used. -/
theorem successorsFromCertificates (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (progress : ∀ (beta : Type) (Delta : List (Formula beta)) (x g witness : OTerm beta),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (typed comp tau (numeral context) x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (variableObject x)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (certificate src false context x g witness)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (computable comp tau (numeral context) g)))
    (alpha : Type) (Gamma : List (Formula alpha)) (x : OTerm alpha)
    (ht : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) x)))
    (hv : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (variableObject x))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (OriginalNeutralExpansion.computableSuccessors src comp context tau x)) := by
  let g : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let E := edge src false context (x.relabel Sum.inl) g
  let Delta := E :: Gamma.map weaken
  have hi : ∀ h ∈ Gamma, h.relabel Sum.inl ∈ Delta := by
    intro h hh
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨h,hh,rfl⟩)
  have ht' := renameInto ht Sum.inl Delta hi
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hv' := renameInto hv Sum.inl Delta hi
  rw [variableObjectRename] at hv'
  have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta E) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htarget : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (computable comp tau (numeral context) g)) := by
    apply edgeCases src context (x.relabel Sum.inl) g _ he
    intro beta j Theta witness hj hc
    simp only [computableRename,GuardedSourceSyntaxProof.numeralRename]
    have htt := renameInto ht' j Theta hj
    simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at htt
    have hvv := renameInto hv' j Theta hj
    rw [variableObjectRename] at hvv
    exact progress beta Theta ((x.relabel Sum.inl).relabel j) (g.relabel j) witness htt hvv hc
  obtain ⟨htarget⟩ := htarget
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction htarget)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilitySuccessorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilitySuccessorsProof
