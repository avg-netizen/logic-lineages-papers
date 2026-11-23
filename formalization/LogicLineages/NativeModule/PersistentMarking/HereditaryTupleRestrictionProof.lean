module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryNaturalityBridgeTargets
public import LogicLineages.NativeModule.PersistentMarking.HereditaryPrefixCodingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryTupleRestrictionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem restrictedLength (E : Environment) (Δ Θ : Context) (ds : List Ty) (vs : List Code)
    (h : ds.length = vs.length) : ds.length = (restrictValues E Δ Θ ds vs).length := by
  simp [restrictValues,List.length_zip,h]

theorem zipRestricted (ds : List Ty) (vs : List Code) (f : Ty × Code → Code)
    (h : ds.length = vs.length) :
    ds.zip ((ds.zip vs).map f) = (ds.zip vs).map (fun p => (p.1,f p)) := by
  induction ds generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons v vs => cases h
  | cons ρ ds ih =>
    cases vs with
    | nil => cases h
    | cons v vs =>
      simp only [List.zip_cons_cons,List.map_cons]
      rw [ih vs (Nat.succ.inj h)]

theorem attachedIndices (ds : List Ty) (vs : List Code) (f : Ty × Code → Option Nat) :
    (ds.attach.zip vs).mapM (fun p => f (p.1.val,p.2)) = (ds.zip vs).mapM f := by
  have h : (ds.attach.zip vs).map (Prod.map Subtype.val id) = ds.zip vs := by
    rw [← List.zip_map_left,List.attach_map_subtype_val]
  rw [← h,List.mapM_map]
  rfl

theorem indicesRestricted (E : Environment) (Δ Θ : Context) (ds : List Ty) (vs : List Code)
    (h : ds.length = vs.length) :
    indices E Θ ds (restrictValues E Δ Θ ds vs) =
      (ds.zip vs).mapM (fun p => indexOf ((descriptor E p.1).carriers Θ) ((descriptor E p.1).restrict Δ Θ p.2)) := by
  unfold indices
  rw [if_pos (restrictedLength E Δ Θ ds vs h)]
  unfold restrictValues
  rw [zipRestricted ds vs _ h,List.mapM_map]
  rfl

theorem exactRestriction : HereditaryNaturalityBridgeTargets.TupleRestrictionExact := by
  intro E σ Δ Θ p xs vs hx
  have hv := hx
  rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hv
  have hlen := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 xs vs hv).1.1
  unfold tupleRestrict
  rw [hx]
  change (p.val.1.attach.zip vs).mapM (fun q => indexOf ((descriptor E q.1.val).carriers Θ)
    ((descriptor E q.1.val).restrict Δ Θ q.2)) = _
  rw [attachedIndices p.val.1 vs (fun q => indexOf ((descriptor E q.1).carriers Θ) ((descriptor E q.1).restrict Δ Θ q.2)),indicesRestricted E Δ Θ p.val.1 vs hlen]

end LogicLineages.PersistentMarking.HereditaryTupleRestrictionProof
