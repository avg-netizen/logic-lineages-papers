module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionCoreProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalComputabilityDownwardProof InternalComputabilityApplicationProof
open InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalNeutralExpansion OriginalNeutralTypeInductionSyntaxProof
open OriginalSourceNeutralApplicationSyntaxProof (nonLambdaObjectRename)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)

/-- Finite-type induction is internal to the original combined-body calculus.
The supplier parameters are arithmetic lemmas separately discharged at the
concrete final tuple; none is added to the frozen concrete target. -/
theorem neutral (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (rules : ArithmeticRules src comp context)
    (hcarrier : ∀ (alpha : Type) (tau : Ty) (x : OTerm alpha),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((typed comp tau (numeral context) x).imp (carrier src false context x))))
    (hout : ∀ (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
      (F A X : OTerm alpha),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
        (domain comp context sigma tau F A)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
        (accepted comp sigma tau (numeral context) F A X)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
        (typed comp tau (numeral context) X)))
    (hshape : OriginalApplicationComputability.AcceptedOutputNonLambda comp context)
    (hsucc : ApplicationSuccessorComputability src comp context) :
    ∀ (tau : Ty) (alpha : Type) (Gamma : List (Formula alpha)) (object : OTerm alpha),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) object)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (OriginalSourceNeutralApplication.nonLambdaObject object)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computableSuccessors src comp context tau object)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computable comp tau (numeral context) object)) := by
  intro tau
  induction tau with
  | ground =>
    intro alpha Gamma object ht _ hs
    exact OriginalNeutralTypeInductionLogicProof.ground src comp context hcarrier object ht hs
  | arrow sigma tau ihs iht =>
    intro alpha Gamma object ht hn hs
    apply actualOriginalArrowIntroduction (SourcePresentation.sourceBody src context)
      comp alpha Gamma sigma tau (numeral context) object ht
    let argument : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
    let Delta := computable comp sigma (numeral context) argument ::
      guarded comp (object.relabel Sum.inl) argument :: Gamma.map weaken
    have hi : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
      intro p hp
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    have ht' := renameInto ht Sum.inl Delta hi
    simp only [typedRename,numeralRename] at ht'
    have hn' := renameInto hn Sum.inl Delta hi
    rw [nonLambdaObjectRename] at hn'
    have hs' := renameInto hs Sum.inl Delta hi
    rw [successorsRename] at hs'
    have hca : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (computable comp sigma (numeral context) argument)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hguard : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (guarded comp (object.relabel Sum.inl) argument)) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hdomain : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (domain comp context sigma tau (object.relabel Sum.inl) argument)) :=
      andIntro (andIntro ht' (typedness comp sigma (numeral context) argument hca)) hguard
    have happ := closedApply (rules.applicationTotal (alpha ⊕ Fin 1) sigma tau
      (object.relabel Sum.inl) argument) hdomain
    have hresult : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
        (resultExists comp sigma tau (numeral context) (object.relabel Sum.inl) argument)) := by
      apply applicationCases comp context sigma tau (object.relabel Sum.inl) argument _ happ
      intro beta j Theta out hj ha
      simp only [resultExistsRename,numeralRename]
      have hd := renameInto hdomain j Theta hj
      rw [domainRename] at hd
      have hnn := renameInto hn' j Theta hj
      rw [nonLambdaObjectRename] at hnn
      have hss := renameInto hs' j Theta hj
      rw [successorsRename] at hss
      have hcc := renameInto hca j Theta hj
      simp only [computableRename,numeralRename] at hcc
      have hinputs : Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
          (OriginalNeutralTypeInductionLogicProof.inputs src comp context sigma tau
            ((object.relabel Sum.inl).relabel j) (argument.relabel j) out)) :=
        andIntro (andLeft (andLeft hd)) (andIntro hnn
          (andIntro hss (andIntro (andRight hd) (andIntro hcc ha))))
      have htyped := hout beta Theta sigma tau
        ((object.relabel Sum.inl).relabel j) (argument.relabel j) out hd ha
      obtain ⟨hshape'⟩ := hshape (SourcePresentation.sourceBody src context) beta Theta sigma tau
        ((object.relabel Sum.inl).relabel j) (argument.relabel j) out
      obtain ⟨hda⟩ := andIntro hd ha
      have hnout : Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
          (OriginalSourceNeutralApplication.nonLambdaObject out)) :=
        ⟨Derivation.implicationElimination hshape' hda⟩
      have hsout := OriginalNeutralTypeInductionLogicProof.applicationSuccessors src comp context hsucc
        sigma tau ((object.relabel Sum.inl).relabel j) (argument.relabel j) out hinputs
      have hc := iht beta Theta out htyped hnout hsout
      exact resultIntroduction comp sigma tau (numeral context)
        ((object.relabel Sum.inl).relabel j) (argument.relabel j) out ha hc
    simpa only [numeralRename] using hresult

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionCoreProof
