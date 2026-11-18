import LogicLineages.PersistentMarking.HereditaryTupleRoundtripProof
namespace LogicLineages.PersistentMarking.HereditaryTupleAdapterProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem attachedMapM (ds : List Ty) (is : List Nat) (f : Ty × Nat → Option Code) :
    (ds.attach.zip is).mapM (fun p => f (p.1.val,p.2)) = (ds.zip is).mapM f := by
  have h : (ds.attach.zip is).map (Prod.map Subtype.val id) = ds.zip is := by
    rw [← List.zip_map_left,List.attach_map_subtype_val]
  rw [← h,List.mapM_map]
  rfl

/- Canonical smaller-type descriptors ignore the local proof of properness;
this is an actual equation of algorithms, not merely proof irrelevance of
an arbitrary callback. -/
theorem tupleDecodeCanonical (E : Environment) (σ : Ty) (Δ : Context) (p : Prefix σ) (is : List Nat) :
    tupleDecode σ (canonicalLower E σ) Δ p is = HereditaryDomainSemantics.values E Δ p.val.1 is := by
  unfold tupleDecode HereditaryDomainSemantics.values
  by_cases h : is.length = p.val.1.length
  · simp only [h,h.symm,if_true,canonicalLower]
    exact attachedMapM p.val.1 is (fun q => ((descriptor E q.1).carriers Δ)[q.2]?)
  · have hn : p.val.1.length ≠ is.length := Ne.symm h
    simp only [h,hn,if_false]

end LogicLineages.PersistentMarking.HereditaryTupleAdapterProof
