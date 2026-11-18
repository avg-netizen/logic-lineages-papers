import LogicLineages.PersistentMarking.HereditaryCombineCoordinateProof
namespace LogicLineages.PersistentMarking.HereditaryCombineEncodingProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryEncodeCoordinateProof

theorem atContextEncoding (E : Environment) (σ : Ty) (Γ Δ : Context) (meet : Bool) (cs : List Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) :
    (atContext σ (lowerCodes σ (canonicalLower E σ)) E.names E.ports E.target Δ).map
      (coordinate E (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ)))) =
    combineAt E σ (canonicalLower E σ) Γ Δ meet cs := by
  let v := aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ))
  let obs := distinctObservations (DecisionObservations.observations E.names E.ports Δ E.target σ)
  have hbit := HereditaryCombineCoordinateProof.bitCoordinate E σ Γ Δ meet cs hw he hc
  have hav := hbit .available (by simp [HereditaryOrderBitProof.bits])
  have hwk : obs.map (fun t => coordinate E v (⟨Δ,.weak t⟩,2)) =
      obs.map (fun t => bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.weak t⟩).getD 0))) := by
    apply List.map_congr_left
    intro t ht
    exact hbit (.weak t) (by simp only [HereditaryOrderBitProof.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map]; exact Or.inl (Or.inr ⟨t,ht,rfl⟩))
  have hst : obs.map (fun t => coordinate E v (⟨Δ,.strict t⟩,2)) =
      obs.map (fun t => bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.strict t⟩).getD 0))) := by
    apply List.map_congr_left
    intro t ht
    exact hbit (.strict t) (by simp only [HereditaryOrderBitProof.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map]; exact Or.inr ⟨t,ht,rfl⟩)
  have happ : (fullPrefixes σ).attach.flatMap (fun p =>
      (vectors (tupleBounds σ (canonicalLower E σ) Δ p)).map (fun is =>
        coordinate E v (⟨Δ,.application p.val.1 p.val.2 is⟩,
          outputBound σ (lowerCodes σ (canonicalLower E σ)) Δ p.val.1 p.val.2 p.property))) =
      (fullPrefixes σ).attach.flatMap (fun p =>
      (vectors (tupleBounds σ (canonicalLower E σ) Δ p)).map (fun is =>
        (indexOf ((descriptor E p.val.2).carriers Δ)
          (if meet then (descriptor E p.val.2).meet Δ (cs.filterMap (output E σ (canonicalLower E σ) Γ Δ p is))
           else (descriptor E p.val.2).join Δ (cs.filterMap (output E σ (canonicalLower E σ) Γ Δ p is)))).getD 0)) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    apply List.map_congr_left
    intro is his
    exact HereditaryCombineCoordinateProof.application E σ Γ Δ p meet cs is hw he hc his
  simp only [atContext,combineAt,List.map_append,List.map_cons,List.map_nil,List.map_map,
    List.map_flatMap,Function.comp_def]
  change (([coordinate E v (⟨Δ,.available⟩,2)] ++ obs.map (fun t => coordinate E v (⟨Δ,.weak t⟩,2))) ++
    obs.map (fun t => coordinate E v (⟨Δ,.strict t⟩,2))) ++ _ = _
  rw [hav,hwk,hst]
  exact congrArg (fun tail =>
    (([bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.available⟩).getD 0))] ++
    obs.map (fun t => bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.weak t⟩).getD 0)))) ++
    obs.map (fun t => bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.strict t⟩).getD 0)))) ++ tail) happ


theorem encoding : CombineEncoding := by
  intro E σ Γ meet cs hΓ lower hc
  rw [encodeMap]
  unfold combine layout schema
  rw [List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro Δ hd
  obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mp hd
  exact (atContextEncoding E σ Γ Δ meet cs hw he hc).symm
end LogicLineages.PersistentMarking.HereditaryCombineEncodingProof
