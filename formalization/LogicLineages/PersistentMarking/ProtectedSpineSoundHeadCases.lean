import LogicLineages.PersistentMarking.ProtectedSpineSoundHeadFrameProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundHeadSyntaxProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundOrdinaryProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundHeadCases
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineLaws ProtectedSpineSoundInterpreterTargets
open ProtectedSpineSoundHeadFrameProof

theorem marked (F : Inputs S) (M : Code) (f : Head) (σ : Ty) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads) (hM : FamilyRelated F M)
    (ih : ArgsGoal F M bs) (ih' : ArgsGoal F M es) : ExprGoal F M (.marked f σ bs es) := by
  intro Γ types vs cs ht hu hw hf
  let E := domain F
  let p := ownerParameter F M f σ Γ cs bs es
  let newBase := substituteArgs vs 0 bs
  let newExtras := substituteArgs vs 0 es
  have ho := instantiatedOwner F M f σ Γ types vs cs bs es hm ht hu hw hf ih ih'
  constructor
  · exact ProtectedSpineSoundBuilderProof.build F M p newBase newExtras hm ho hM
  · intro consumed outer hSub ds τ xs args hp hx hTyped hSource hRelated
    cases ds with
    | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
    | cons d ds =>
      cases xs with
      | nil => have h := hx.1; simp at h
      | cons x xs =>
        change Related F τ Γ (originalHeadCall E F.data.sourceHeads M Γ f σ p.2.2.2.1 p.2.2.2.2 (d::ds) (x::xs) τ)
          (applyAux (substitute outer consumed.length (.marked f σ bs es)) args consumed)
        rw [ProtectedSpineSoundHeadSyntaxProof.marked f σ bs es consumed outer args,←hSub]
        exact ProtectedSpineSoundTupleProof.marked F M f σ τ Γ p.2.2.2.1 p.2.2.2.2 newBase newExtras
          args (d::ds) (x::xs) hm ho hM hp hx hTyped hSource hRelated

theorem ordinary (F : Inputs S) (M : Code) (f : Head) (bs : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads) (hM : FamilyRelated F M)
    (ih : ArgsGoal F M bs) : ExprGoal F M (.head f bs) := by
  intro Γ types vs cs ht hu hw hf
  let E := domain F
  let p := ownerParameter F M f f.result Γ cs bs .nil
  let newBase := substituteArgs vs 0 bs
  have hMarkedTyped := SpineMarkingProof.markTyped (BoundContext.prefix types EmptyContext) (.head f bs)
    f.result (.marked f f.result bs .nil) ht rfl
  have hMarked := DecisionSourceMarkProof.sourceMark _ _ _ _ (.head f bs) (.marked f f.result bs .nil) hu rfl
  have ho := instantiatedOwner F M f f.result Γ types vs cs bs .nil hm hMarkedTyped hMarked hw hf ih (nilArgs F M)
  constructor
  · exact ProtectedSpineSoundOrdinaryProof.codeRelated F M f Γ p.2.2.2.1 p.2.2.2.2 newBase hm ho hM
  · intro consumed outer hSub ds τ xs args hp hx hTyped hSource hRelated
    cases ds with
    | nil => exact False.elim ((FinitePrefixProof.forward _ _ _ hp).1 rfl)
    | cons d ds =>
      cases xs with
      | nil => have h := hx.1; simp at h
      | cons x xs =>
        change Related F τ Γ (originalHeadCall E F.data.sourceHeads M Γ f f.result p.2.2.2.1 p.2.2.2.2 (d::ds) (x::xs) τ)
          (applyAux (substitute outer consumed.length (.head f bs)) args consumed)
        rw [ProtectedSpineSoundHeadSyntaxProof.ordinary f bs consumed outer args,←hSub]
        change Related F τ Γ _ (apply (.head f newBase) args)
        rw [ProtectedSpineSoundTupleProof.ordinaryCall f τ newBase args
          (ProtectedSpineSoundTupleProof.nonempty hp hTyped) hTyped]
        exact ProtectedSpineSoundTupleProof.marked F M f f.result τ Γ p.2.2.2.1 p.2.2.2.2 newBase .nil
          args (d::ds) (x::xs) hm ho hM hp hx hTyped hSource hRelated

end LogicLineages.PersistentMarking.ProtectedSpineSoundHeadCases
