module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSelectSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessSelectProof
open Spine DecisionPorts DecisionRequests FiniteDomainSchema FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets ProtectedSpineSelectSupport
open MarkedConstructorOperator (step)

theorem nonempty {S : Signature} (F : Inputs S) (M : Code) (Γ : Context)
    (f : Head) (τ : Ty) (bs es : Args) (q t r : Expr) (ds : List Ty)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M)
    (hBase : BaseTyped EmptyContext bs f.arguments) (hExtras : ExtrasTyped EmptyContext es)
    (hτ : PaperTerm S t τ) (hds : ds ≠ [])
    (hCall : Invariant F (.fullCall Γ q (ArrowPrefix ds τ) (ownerCopies f bs es ds) τ t))
    (hApply : apply q (ownerCopies f bs es ds) = some r)
    (hTree : PortComparison.Weak S F.data.types F.data.names Γ r t)
    (ih : WeakGoal F M Γ r t) :
    ∃ xs, (ds,τ) ∈ fullPrefixes q.type ∧
      MarkedConstructorTests.ownerTuple (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es) ds = some xs ∧
      (decode (domain F) τ Γ
        (StructuralActions.fullAction (domain F) q.type Γ
          (concreteOutput S (domain F) F.data.sourceHeads M Γ q.type (some q)) ds τ xs)).weak Γ t = true := by
  let E := domain F
  let H := F.data.sourceHeads
  let args := ownerCopies f bs es ds
  let xs := (concreteTags S F M Γ args).map Prod.snd
  have hChild := DecisionClosureCallProof.result S F Γ q (ArrowPrefix ds τ) args τ t r hApply hCall
  obtain ⟨hw,hQ,hArgs,hO,hSType,hRType,hQT,hAT⟩ := hCall
  have hQType := SpineShiftProof.annotationExact EmptyContext q _ hQT
  have hPre := (FinitePrefixProof.exactPrefix q.type ds τ).mpr ⟨hds,hQType.symm⟩
  have hQTy : Typed EmptyContext q q.type := hQType.symm ▸ hQT
  have hATy : CallTyped EmptyContext q.type args τ := hQType.symm ▸ hAT
  have hArgsCov := sourcesCovered S F Γ args hArgs
  have hArgsTyped := (ProtectedSpineConcreteInputProof.argumentTypes q.type args τ hATy).1
  have hInputs := ProtectedSpineConcreteInputProof.codeValid S E H M Γ args (domainTypes args)
    (prefixClosed S F) hm hw ⟨hArgsTyped,hArgsCov⟩
  have hD : domainTypes args = ds := copyDomains f bs es ds
  have hx : TupleValues E Γ ds xs := hD ▸ hInputs.2
  have hFull := fullTable S F M Γ q ds τ xs hm hw hQ hQTy hPre hx
  have hApplyFixed := ProtectedSpineFixedApplicationProof.exact_FixedApplication S E H M Γ q args τ
    (prefixClosed S F) hm hfix hw hQTy (sourceCovered S F Γ q hQ) hATy hArgsCov
  rw [hD,hApply] at hApplyFixed
  have hRes := hFull.trans hApplyFixed
  have ht := ProtectedSpineAdequacyTypingProof.weak S F.data.types F.data.names Γ r t hTree
  have hR : r.type = τ := ht.2.2.trans (SpineShiftProof.annotationExact _ _ _ hτ.1)
  have hBit := (rootBits S F M Γ r t hm hChild.1 hChild.2.1 ht.1.1 hChild.2.2 ht.2.2).1.trans (ih hChild)
  have hOut : (decode E τ Γ (concreteOutput S E H M Γ τ (some r))).weak Γ t = true := by
    rw [← hR]
    exact hBit
  exact ⟨xs,hPre,ownerValues S F M Γ f τ bs es ds hm hfix hw hBase hExtras hArgs,by rw [hRes]; exact hOut⟩

theorem select {S : Signature} (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty)
    (bs es : Args) (q t r : Expr) (i : Nat) (ds : List Ty)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M)
    (hs : PaperTerm S (.marked f τ bs es) τ) (ht : PaperTerm S t τ)
    (hAt : At bs i q ∨ At es i q) (hQ : Typed EmptyContext q (ArrowPrefix ds τ))
    (hApply : apply q (ownerCopies f bs es ds) = some r)
    (hTree : PortComparison.Weak S F.data.types F.data.names Γ r t)
    (ih : WeakGoal F M Γ r t) : WeakGoal F M Γ (.marked f τ bs es) t := by
  intro h
  let E := domain F
  let H := F.data.sourceHeads
  let p := ownerAt S F M Γ f τ bs es
  let a : MarkedExtras.Tagged := (q.type,concreteOutput S E H M Γ q.type (some q))
  have hArg := DecisionClosureCallProof.selection S F Γ f τ bs es t q i ds hs ht hAt hQ h
  have hQT := SpineShiftProof.annotationExact _ _ _ hQ
  have hMem := membership S F M Γ f τ bs es q i hm h.1 h.2.1 hs.1 hArg.2.1 (hQT.symm ▸ hQ) hAt
  have hp := ProtectedSpineAdequacyOwnerProof.valid S F M Γ f τ bs es hm h.1 h.2.1 hs.1
  have hWitness : MarkedConstructorTargets.SelectWitness E H M p t := by
    refine ⟨a,hMem,?_⟩
    cases ds with
    | nil =>
      have he : q = r := Option.some.inj hApply
      subst r
      have hChild := DecisionClosureCallProof.result S F Γ q (ArrowPrefix [] τ) (ownerCopies f bs es [])
        τ t q hApply hArg
      have hTypes := ProtectedSpineAdequacyTypingProof.weak S F.data.types F.data.names Γ q t hTree
      exact Or.inl ⟨hQT,ProtectedSpineAdequacyTypingProof.taggedBit S F M Γ q t hm
        hChild.1 hChild.2.1 hChild.2.2 hTypes false (ih hChild)⟩
    | cons d ds =>
      have hBaseExtra : BaseTyped EmptyContext bs f.arguments ∧ ExtrasTyped EmptyContext es := by
        cases hs.1 with
        | marked hb he => exact ⟨hb,he⟩
      obtain ⟨xs,hPre,hSome,hBit⟩ := nonempty F M Γ f τ bs es q t r (d::ds) hm hfix
        hBaseExtra.1 hBaseExtra.2 ht (by simp) hArg hApply hTree ih
      exact Or.inr ⟨d::ds,xs,hPre,hSome,hBit⟩
  have hTest := (MarkedConstructorSelectProof.select E H M p t).mpr hWitness
  rw [ProtectedSpineAdequacyOwnerProof.rootEq S F M Γ f τ bs es hp]
  change MarkedConstructorTests.weakTest S E H M p t = true
  simp [MarkedConstructorTests.weakTest,hTest]

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessSelectProof
