import LogicLineages.PersistentMarking.HereditaryLatticeTargets
import LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
namespace LogicLineages.PersistentMarking.HereditaryCombineOutputProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryDecodedValiditySupport

theorem filterMapEq {α β : Type} (f : α → Option β) (g : α → β) (xs : List α)
    (h : ∀ x, x ∈ xs → f x = some (g x)) : xs.filterMap f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,h x List.mem_cons_self,List.map_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem outputs (E : Environment) (σ : Ty) (Γ Δ : Context) (p : Prefix σ)
    (is : List Nat) (vs : List Code) (cs : List Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ)
    (hi : tupleDecode σ (canonicalLower E σ) Δ p is = some vs) :
    cs.filterMap (output E σ (canonicalLower E σ) Γ Δ p is) =
      cs.map (fun c => (HereditaryDomainSemantics.decode E σ Γ c).application Δ p.val.1 p.val.2 vs) := by
  apply filterMapEq
  intro c hm
  have hiv := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mpr ⟨vs,hi⟩
  obtain ⟨out,ho,hom⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p is c hw he (hc c hm) hiv
  rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hi
  have hind := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 is vs hi).2
  rw [decodedOutput E σ Γ Δ p c is vs out hind ho]
  exact ho

end LogicLineages.PersistentMarking.HereditaryCombineOutputProof
