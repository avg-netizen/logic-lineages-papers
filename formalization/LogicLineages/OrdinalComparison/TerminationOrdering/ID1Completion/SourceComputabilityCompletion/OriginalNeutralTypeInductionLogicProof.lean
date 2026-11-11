module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionLogicProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalAccessibilityRules OriginalNeutralExpansion
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalComputabilityDownwardProof InternalComputabilityApplicationProof
open InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open OriginalNeutralTypeInductionSyntaxProof
open OriginalSourceNeutralApplicationSyntaxProof (nonLambdaObjectRename)
open SourceComputabilityFormulaSupportProof (numeral allOne)
open GuardedSourceSyntaxProof (numeralRename)

/-- Precisely the original function/argument/application inputs, before an
original source certificate is chosen. -/
def inputs {alpha : Type} (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty) (f a out : OTerm alpha) : Formula alpha :=
  typed comp (.arrow sigma tau) (numeral context) f ⊓
    (OriginalSourceNeutralApplication.nonLambdaObject f ⊓
      (computableSuccessors src comp context (.arrow sigma tau) f ⊓
        (guarded comp f a ⊓ (computable comp sigma (numeral context) a ⊓
          accepted comp sigma tau (numeral context) f a out))))

theorem inputsRename {alpha beta : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (f a out : OTerm alpha) (j : alpha → beta) :
    (inputs src comp context sigma tau f a out).relabel j =
      inputs src comp context sigma tau (f.relabel j) (a.relabel j) (out.relabel j) := by
  simp only [inputs,conjunctionRename,typedRename,nonLambdaObjectRename,
    successorsRename,guardedRename,computableRename,acceptedRename,numeralRename]

/-- Turn the original certificate successor consumer into its original
existential-edge/all-successors formulation. -/
theorem applicationSuccessors (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (hsucc : ApplicationSuccessorComputability src comp context)
    {alpha : Type} {Gamma : List (Formula alpha)} (sigma tau : Ty) (f a out : OTerm alpha)
    (hi : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (inputs src comp context sigma tau f a out))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computableSuccessors src comp context tau out)) := by
  let target : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let P := edge src false context (out.relabel Sum.inl) target
  let Delta := P :: Gamma.map weaken
  have hj : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hi' := renameInto hi Sum.inl Delta hj
  rw [inputsRename] at hi'
  have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (computable comp tau (numeral context) target)) := by
    apply edgeCases src context (out.relabel Sum.inl) target _ he
    intro beta j Theta witness hk hw
    simp only [computableRename,numeralRename]
    have hh := renameInto hi' j Theta hk
    rw [inputsRename] at hh
    have harg := andRight (andRight (andRight hh))
    have hacc := andRight (andRight harg)
    have hpre : Nonempty (Derivation (SourcePresentation.sourceBody src context) Theta
        (applicationPremises src comp context sigma tau
          ((f.relabel Sum.inl).relabel j) ((a.relabel Sum.inl).relabel j)
          ((out.relabel Sum.inl).relabel j) (target.relabel j) witness)) :=
      andIntro (andLeft hh) (andIntro (andLeft (andRight hh))
        (andIntro (andLeft (andRight (andRight hh)))
          (andIntro (andLeft harg) (andIntro (andLeft (andRight harg)) (andIntro hacc hw)))))
    obtain ⟨h⟩ := hsucc beta Theta sigma tau
      ((f.relabel Sum.inl).relabel j) ((a.relabel Sum.inl).relabel j)
      ((out.relabel Sum.inl).relabel j) (target.relabel j) witness
    obtain ⟨hpre⟩ := hpre
    exact ⟨Derivation.implicationElimination h hpre⟩
  obtain ⟨hc⟩ := hc
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hc)⟩

/-- Ground neutral expansion uses actual original accessibility introduction;
its original computable successors supply the membership component. -/
theorem ground (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat)
    (hcarrier : ∀ (alpha : Type) (tau : Ty) (x : OTerm alpha),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((typed comp tau (numeral context) x).imp (carrier src false context x))))
    {alpha : Type} {Gamma : List (Formula alpha)} (object : OTerm alpha)
    (ht : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp .ground (numeral context) object)))
    (hs : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computableSuccessors src comp context .ground object))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computable comp .ground (numeral context) object)) := by
  have hc := closedApply (hcarrier alpha .ground object) ht
  let target : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let P := edge src false context (object.relabel Sum.inl) target
  let Delta := P :: Gamma.map weaken
  have hj : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hs' := renameInto hs Sum.inl Delta hj
  rw [successorsRename] at hs'
  have he : Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hct := successorApply src comp context .ground (object.relabel Sum.inl) target hs' he
  rw [computableGround] at hct
  obtain ⟨hi⟩ := andRight hct
  have hsI : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (successors src false context object)) :=
    ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hi)⟩
  have hi := InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction
    src false context alpha Gamma object hc hsI
  rw [computableGround]
  exact andIntro ht hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionLogicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionLogicProof
