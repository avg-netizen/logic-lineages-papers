module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleAdapterProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleBoundsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryPrefixCodingProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem boundsCanonical (E : Environment) (σ : Ty) (Δ : Context) (p : Prefix σ) :
    tupleBounds σ (canonicalLower E σ) Δ p =
      p.val.1.map (fun ρ => ((descriptor E ρ).carriers Δ).length) := by
  change p.val.1.attach.map (fun ρ => ((descriptor E ρ.val).carriers Δ).length) = _
  have h := congrArg (List.map (fun ρ => ((descriptor E ρ).carriers Δ).length))
    (List.attach_map_subtype_val p.val.1)
  simpa only [List.map_map,Function.comp_def] using h

theorem decodeExact (E : Environment) (σ : Ty) (Δ : Context) (p : Prefix σ) (is : List Nat) :
    is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p) ↔
      ∃ vs, tupleDecode σ (canonicalLower E σ) Δ p is = some vs := by
  rw [boundsCanonical,FiniteVectorProof.exactVector,HereditaryTupleAdapterProof.tupleDecodeCanonical]
  constructor
  · exact HereditaryTupleBoundsProof.decodeFits E Δ p.val.1 is
  · rintro ⟨vs,hvs⟩
    exact HereditaryTupleBoundsProof.fitsDecode E Δ p.val.1 is vs hvs

end LogicLineages.PersistentMarking.HereditaryPrefixCodingProof
