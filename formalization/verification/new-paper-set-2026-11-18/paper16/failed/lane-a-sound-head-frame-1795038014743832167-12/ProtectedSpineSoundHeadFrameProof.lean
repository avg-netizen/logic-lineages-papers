import LogicLineages.PersistentMarking.ProtectedSpineSoundFrameProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundListProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundSourceProof
import LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundHeadFrameProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineLaws
open ProtectedSpineInterpreter ProtectedSpineInterpreterCore ProtectedSpineSoundInterpreterTargets
open ProtectedSpineSoundStageTargets ProtectedSpineSoundSourceProof
open MarkedFamilyParameters (Parameter)

def ownerParameter (F : Inputs S) (M : Code) (f : Head) (σ : Ty) (Γ : Context)
    (cs : ProtectedSpineEnvironment.BoundValues) (bs es : Args) : Parameter :=
  parameter (domain F) f σ Γ
    (evaluateArgs S (domain F) F.data.sourceHeads M bs Γ [] cs)
    (evaluateArgs S (domain F) F.data.sourceHeads M es Γ [] cs)

theorem instantiatedOwner (F : Inputs S) (M : Code) (f : Head) (σ : Ty) (Γ : Context)
    (types : List Ty) (vs : Args) (cs : ProtectedSpineEnvironment.BoundValues) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hq : Typed (BoundContext.prefix types EmptyContext) (.marked f σ bs es) σ)
    (hu : Source F Γ (.marked f σ bs es)) (hw : WellFormed F.data.types F.data.ports Γ)
    (hf : Frame F Γ types vs cs) (hB : ArgsGoal F M bs) (hE : ArgsGoal F M es) :
    OwnerRelated F (ownerParameter F M f σ Γ cs bs es) (substituteArgs vs 0 bs) (substituteArgs vs 0 es) := by
  let E := domain F
  let H := F.data.sourceHeads
  let C := BoundContext.prefix types EmptyContext
  let a : Assignments := ⟨[],cs⟩
  let base := evaluateArgs S E H M bs Γ [] cs
  let extras := evaluateArgs S E H M es Γ [] cs
  have hInput := ProtectedSpineSoundFrameProof.inputs F Γ types vs cs hw hf
  have hSub := ProtectedSpineSoundFrameProof.concreteTyped types vs hf.1 (.marked f σ bs es) hq
  have hSource := ProtectedSpineSoundFrameProof.concreteSource F Γ types vs (.marked f σ bs es) hq hf.1 hu hf.2.1
  have hPaper : PaperTerm S (.marked f σ (substituteArgs vs 0 bs) (substituteArgs vs 0 es)) σ :=
    ⟨hSub,validSource F Γ _ hSource⟩
  have hCov := sourceCovered S F Γ (.marked f σ bs es) hu
  have hBS := DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ hu
  have hES := DecisionSourceBasicProof.markedExtras _ _ _ _ _ _ _ _ hu
  have hBC := ProtectedSpineCoverageProof.markedBase E H f σ bs es hCov
  have hEC := ProtectedSpineCoverageProof.markedExtras E H f σ bs es hCov
  cases hq with
  | marked hBase hExtra =>
    have hBaseLaw := ProtectedSpineInterpretationProof.baseLaws S E H M (prefixClosed S F) hm C
      bs f.arguments hBase hBC
    have hExtraLaw := ProtectedSpineInterpretationProof.extraLaws S E H M (prefixClosed S F) hm C es hExtra hEC
    have hTypes := ProtectedSpineCoverageProof.argumentTypes E H es hEC
    have hETag := ProtectedSpineArgumentProof.tags E Γ _ _ a hExtraLaw hInput hTypes
    have hEq := hBaseLaw.types_eq Γ a
    have hBaseRelated := hB Γ types vs cs (DecisionOccurrenceProof.baseExtras _ _ _ hBase) hBS hw hf
    have hExtraRelated := hE Γ types vs cs hExtra hES hw hf
    have hP : MarkedFamilyParameters.Valid E H (ownerParameter F M f σ Γ cs bs es) :=
      ⟨hu.2.1 f List.mem_cons_self,DecisionSourceBasicProof.rootType _ _ _ _ _ hu,hw,
        hBaseLaw.valid Γ a hInput,MarkedExtrasDownProof.downExtra E Γ extras hw hETag⟩
    have hZip : f.arguments.zip (base.map Prod.snd) = base := by
      change base.map Prod.fst = f.arguments at hEq
      rw [←hEq,ProtectedSpineArgumentProof.zipProjections]
    refine ⟨hP,hPaper,hSource,?_,?_⟩
    · change BaseRelated F Γ (f.arguments.zip (base.map Prod.snd)) (substituteArgs vs 0 bs)
      rw [hZip]
      exact hBaseRelated
    · intro b hb
      obtain ⟨hValid,c,hc,hle⟩ := (MarkedExtrasFoundationProof.downExact E Γ extras b).mp hb
      obtain ⟨i,q,hAt,hTy,hQ⟩ := ProtectedSpineSoundListProof.baseMember F Γ hExtraRelated hc
      obtain ⟨hT,hR⟩ := ProtectedSpineSoundOwnerProof.downTag F Γ b c q hw hValid hle hQ
      exact ⟨i,q,hAt,hT.trans hTy,hR⟩

theorem nilArgs (F : Inputs S) (M : Code) : ArgsGoal F M .nil := by
  intros
  exact .nil

theorem consArgs (F : Inputs S) (M : Code) (q : Expr) (qs : Args)
    (ih : ExprGoal F M q) (ih' : ArgsGoal F M qs) : ArgsGoal F M (.cons q qs) := by
  intro Γ types vs cs ht hu hw hf
  cases ht with
  | cons ht ht' =>
    have hType := SpineShiftProof.annotationExact _ _ _ ht
    have htq : Typed (BoundContext.prefix types EmptyContext) q q.type := hType.symm ▸ ht
    have hq := (ih Γ types vs cs htq hu.1 hw hf).1
    have hqs := ih' Γ types vs cs ht' hu.2 hw hf
    have hSubTy := ProtectedSpineSoundFrameProof.typeTag types vs hf.1 q htq
    change BaseRelated F Γ
      ((q.type,codeAt (domain F) q.type (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],cs⟩)::
        evaluateArgs S (domain F) F.data.sourceHeads M qs Γ [] cs)
      (.cons (substitute vs 0 q) (substituteArgs vs 0 qs))
    generalize hc : codeAt (domain F) q.type (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],cs⟩ = c at hq ⊢
    have hr : ProtectedSpineSoundRelation.Related F (substitute vs 0 q).type Γ c (some (substitute vs 0 q)) :=
      hSubTy.symm ▸ hq
    simpa only [hSubTy] using BaseRelated.cons hr hqs

end LogicLineages.PersistentMarking.ProtectedSpineSoundHeadFrameProof
