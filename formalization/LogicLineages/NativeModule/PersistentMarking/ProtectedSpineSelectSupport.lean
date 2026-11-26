module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyOwnerProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineListTransportProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureCallProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSelectSupport
open Spine NameBridge DecisionPorts FiniteDomainSchema FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineCompletenessTargets
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets
open MarkedConstructorOperator (step)

theorem copyDomains (f : Head) (bs es : Args) (ds : List Ty) :
    domainTypes (ownerCopies f bs es ds) = ds := by
  induction ds with
  | nil => rfl
  | cons σ ds ih =>
    change σ :: domainTypes (ownerCopies f bs es ds) = σ::ds
    rw [ih]

theorem ownerValues (S : Signature) (F : Inputs S) (M : Code) (Γ : Context)
    (f : Head) (τ : Ty) (bs es : Args) (ds : List Ty)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hfix : step S (domain F) F.data.sourceHeads M = M)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hBase : BaseTyped EmptyContext bs f.arguments) (hExtras : ExtrasTyped EmptyContext es)
    (hCopy : Sources F Γ (ownerCopies f bs es ds)) :
    MarkedConstructorTests.ownerTuple (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es) ds =
      some ((concreteTags S F M Γ (ownerCopies f bs es ds)).map Prod.snd) := by
  induction ds with
  | nil => rfl
  | cons σ ds ih =>
    have hp := ProtectedSpineAdequacyOwnerProof.previous S F M Γ f σ bs es hm hfix hw hCopy.1
      (Typed.marked hBase hExtras)
    have ht := ih hCopy.2
    change ds.mapM (MarkedConstructorTests.owner (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es)) =
      some ((concreteTags S F M Γ (ownerCopies f bs es ds)).map Prod.snd) at ht
    have hp' : MarkedConstructorTests.owner (domain F) F.data.sourceHeads M (ownerAt S F M Γ f τ bs es) σ =
        some (concreteOutput S (domain F) F.data.sourceHeads M Γ σ (some (.marked f σ bs es))) := hp
    simp [MarkedConstructorTests.ownerTuple,List.mapM_cons,hp',ht,ownerCopies,concreteTags,closedCodes,evaluateArgs,
      concreteOutput]
    rfl

theorem membership (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty)
    (bs es : Args) (q : Expr) (i : Nat)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hOwner : Source F Γ (.marked f τ bs es))
    (hOwnerTy : Typed EmptyContext (.marked f τ bs es) τ) (hq : Source F Γ q) (hqTy : Typed EmptyContext q q.type)
    (hAt : At bs i q ∨ At es i q) :
    (q.type,concreteOutput S (domain F) F.data.sourceHeads M Γ q.type (some q)) ∈
      f.arguments.zip (ownerAt S F M Γ f τ bs es).2.2.2.1 ++ (ownerAt S F M Γ f τ bs es).2.2.2.2 := by
  let E := domain F
  let a : MarkedExtras.Tagged :=
    (q.type,concreteOutput S E F.data.sourceHeads M Γ q.type (some q))
  rcases hAt with h | h
  · apply List.mem_append_left
    rw [ProtectedSpineAdequacyOwnerProof.unchangedBase S F M Γ f τ bs es hm hw hOwner hOwnerTy]
    exact ProtectedSpineListTransportProof.atTag S F M Γ h
  · apply List.mem_append_right
    change a ∈ MarkedExtras.down E Γ (concreteTags S F M Γ es)
    have hmData := DecisionSourceBasicProof.rootType _ _ _ _ _ hq
    have hLaw := ProtectedSpineInterpretationProof.laws S E F.data.sourceHeads M (prefixClosed S F) hm
      EmptyContext q q.type hqTy (sourceCovered S F Γ q hq)
    have hc := (ProtectedSpineEncodingProof.encodeAt E q.type _ hLaw Γ ⟨[],[]⟩
      (ProtectedSpineConcreteInputProof.emptyValid E Γ hw)).1
    have hu := (MarkedExtrasFoundationProof.universeExact E Γ a.1 a.2).mpr ⟨hmData,hc⟩
    exact (MarkedExtrasFoundationProof.downExact E Γ _ a).mpr
      ⟨hu,a,ProtectedSpineListTransportProof.atTag S F M Γ h,(MarkedExtrasFoundationProof.order E Γ hw).1 a hu⟩

theorem fullTable (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q : Expr)
    (ds : List Ty) (τ : Ty) (xs : List Code)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hSource : Source F Γ q) (ht : Typed EmptyContext q q.type)
    (hp : (ds,τ) ∈ fullPrefixes q.type) (hx : TupleValues (domain F) Γ ds xs) :
    StructuralActions.fullAction (domain F) q.type Γ
        (concreteOutput S (domain F) F.data.sourceHeads M Γ q.type (some q)) ds τ xs =
      call S (domain F) F.data.sourceHeads M q Γ [] [] ds xs τ := by
  let E := domain F
  let H := F.data.sourceHeads
  have hv := stageEq S F M Γ q hm hw hSource ht
  have he := (hv Γ hw (DecisionPortsProof.extensionRefl Γ)).2.2 ds τ hp xs hx
  have hTable := ProtectedSpineTableProof.table S E H M EmptyContext q q.type (prefixClosed S F) hm ht
    (sourceCovered S F Γ q hSource) Γ ⟨[],[]⟩ (ProtectedSpineConcreteInputProof.emptyValid E Γ hw) ds τ xs hp hx
  have h := he.trans hTable.symm
  cases ds with
  | nil => exact False.elim ((FinitePrefixProof.forward q.type [] τ hp).1 rfl)
  | cons d ds =>
    cases xs with
    | nil => cases hx.1
    | cons x xs => exact h

end LogicLineages.PersistentMarking.ProtectedSpineSelectSupport
