module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundCallSyntaxProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundBitProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundLiteralProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyBase
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundLambdaStrictProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundSourceProof
public import LogicLineages.NativeModule.PersistentMarking.PortLambdaStateProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorCanonicalOpeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaBitsProof
open Spine NameBridge DecisionPorts DecisionObservations ObservationLambda
open FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineInterpreterCore ProtectedSpineLaws
open ProtectedSpineSoundInterpreterTargets

theorem bit (F : Inputs S) (M : Code) (α : Ty) (body : Expr) (ih : ExprGoal F M body)
    (Γ Δ : Context) (types : List Ty) (vs : Args) (cs : BoundValues)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hf : Frame F Γ types vs cs)
    (ht : Typed (BoundContext.prefix (α::types) EmptyContext) body body.type)
    (hu : Source F Γ (.lam α body))
    (hd : WellFormed F.data.types F.data.ports Δ) (he : Extends Γ Δ) (t : Expr)
    (hObs : t ∈ observations F.data.names F.data.ports Δ F.target (.arrow α body.type))
    (strict : Bool) (h : lambdaField (domain F) α (evaluate S (domain F) F.data.sourceHeads M body)
      Γ [] cs strict Δ t = true) :
    if strict then Strict S (.lam α (substitute vs 1 body)) t
    else Weak S (.lam α (substitute vs 1 body)) t := by
  cases t <;> simp only [lambdaField,Bool.false_eq_true] at h
  rename_i δ target
  let E := domain F
  let H := F.data.sourceHeads
  let β := body.type
  let src := substitute vs 1 body
  have hTP := ProtectedSpineSoundBitProof.observedPaper F Δ (.arrow α β) (.lam δ target) hObs
  have hAnn := SpineShiftProof.annotationExact _ _ _ hTP.1
  have hTy : δ=α := (Ty.arrow.inj hAnn).1
  subst δ
  have hTObs : Observed F Δ (.lam α target) := by
    unfold Observed
    rw [hAnn]
    exact hObs
  obtain ⟨i,hi,hα,hΘ,hExt,hChild⟩ := PortLambdaStateProof.descent S F Δ α target hd hTObs
  let Θ := openingContext Δ α i
  let x := portName F.data.names i
  let v := Expr.free α x
  let c := literalCode E Θ α x
  have h0 := ObservationPortUpdateProof.firstSound Δ i hi
  have hSlot := MarkedConstructorCanonicalOpeningProof.slotEq Δ i hi
  rw [←MarkedConstructorCanonicalOpeningProof.openingEqFill Δ α i] at hΘ hExt hChild
  have hGt : Extends Γ Θ := DecisionPortsProof.extensionTrans Γ Δ Θ he hExt
  have hFrame := ProtectedSpineSoundFrameProof.restrict F Γ Θ types vs cs hw hΘ hGt hf
  have hFilled : Θ[i]? = some (some α) := by simp [Θ,MarkedConstructorOpeningProof.openingAt,h0]
  have hPort : Source F Θ v := DecisionObservedTypesProof.portUniverse F.data.types F.data.names H Θ α v
    (PortTermStateProof.closed S F) hΘ.2 ⟨i,hFilled,rfl⟩
  have hFrame' : Frame F Θ (α::types) (.cons v vs) ((α,c)::weakenBound E Γ Θ cs) :=
    ⟨.cons .free hFrame.1,⟨hPort,hFrame.2.1⟩,
      BaseRelated.cons (q := v) (c := c) (ProtectedSpineSoundLiteralProof.literalRelated F Θ α x hΘ) hFrame.2.2⟩
  have hBody := DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hu
  have hBodyΘ : Source F Θ body := DecisionSourceBasicProof.weakening _ _ _ _ _ _ hGt hBody
  let a : Assignments := ⟨[],(α,c)::weakenBound E Γ Θ cs⟩
  let e := evaluate S E H M body
  have hCode := (ih Θ (α::types) (.cons v vs) a.bound ht hBodyΘ hΘ hFrame').1
  have hlo := ProtectedSpineInterpretationProof.laws S E H M (ProtectedSpineAdequacyBase.prefixClosed S F) hm _ body β
    ht (ProtectedSpineAdequacyBase.sourceCovered S F Γ body hBody)
  have hDec := (ProtectedSpineEncodingProof.encodeAt E β e hlo Θ a
    (ProtectedSpineSoundFrameProof.inputs F Θ (α::types) (.cons v vs) a.bound hΘ hFrame')).2
  have hTChild := ElementarySupportProof.openingPaper S α β x target hTP
  have hTag := SpineShiftProof.annotationExact _ _ _ hTChild.1
  have hO : openBody α x target ∈ observations F.data.names F.data.ports Θ F.target β := hTag ▸ hChild
  have hEq := (hDec Θ hΘ (DecisionPortsProof.extensionRefl Θ)).2.1 (openBody α x target) hO
  have hDerive := ProtectedSpineSoundBitProof.bits F Θ β (substitute (.cons v vs) 0 body)
    (openBody α x target) (codeAt E β e Θ a) hΘ hO hCode
  have hSrcT : Typed (BoundContext.prefix types EmptyContext) (.lam α body) (.arrow α β) := .lam ht
  have hSrcType := ProtectedSpineSoundFrameProof.concreteTyped types vs hf.1 (.lam α body) hSrcT
  have hSrcΔ := DecisionSourceBasicProof.weakening _ _ _ _ _ _ he hu
  have hConcreteSource := ProtectedSpineSoundFrameProof.concreteSource F Δ types vs (.lam α body) hSrcT
    hf.1 hSrcΔ (ProtectedSpineSoundFrameProof.weakenSources F Γ Δ he vs hf.2.1)
  have hSrcPaper : PaperTerm S (.lam α src) (.arrow α β) :=
    ⟨hSrcType,ProtectedSpineSoundSourceProof.validSource F Δ _ hConcreteSource⟩
  have hFreshSource := PortStateProof.unusedAbsent _ _ _ _ src i α
    (DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hConcreteSource) h0
  have hTargetΔ := PortStateProof.observedUniverse S F Δ (.lam α target) hd hTObs
  have hFreshTarget := PortStateProof.unusedAbsent _ _ _ _ target i α
    (DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hTargetΔ) h0
  have hOpen := ProtectedSpineSoundCallSyntaxProof.openCombined vs α x body
  change (if α=α then match openingSlot Δ with
      | none => false
      | some j => if strict then
          (e.value (openingContext Δ α j) (weakenFree E Γ (openingContext Δ α j) [])
            ((α,literalCode E (openingContext Δ α j) α (portName F.data.names j))::
              weakenBound E Γ (openingContext Δ α j) cs)).strict (openingContext Δ α j)
                (openBody α (portName F.data.names j) target)
        else (e.value (openingContext Δ α j) (weakenFree E Γ (openingContext Δ α j) [])
            ((α,literalCode E (openingContext Δ α j) α (portName F.data.names j))::
              weakenBound E Γ (openingContext Δ α j) cs)).weak (openingContext Δ α j)
                (openBody α (portName F.data.names j) target)
     else false) = true at h
  rw [if_pos rfl,hSlot] at h
  cases strict
  · have hW := hDerive.1 (hEq.1.trans h)
    rw [←hOpen] at hW
    exact Weak.abs hSrcPaper hTP hFreshSource hFreshTarget hW
  · have hS := hDerive.2 (hEq.2.trans h)
    rw [←hOpen] at hS
    exact ProtectedSpineSoundLambdaStrictProof.lift S α β x src target hSrcPaper hTP hFreshSource hFreshTarget hS

end LogicLineages.PersistentMarking.ProtectedSpineSoundLambdaBitsProof
