import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowConstructorStatMarkProof
import LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowPreservationRawProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowExternalComputability
open NumberedWindowExternalComputabilityChecks NumberedWindowConstructorArgumentAddresses
open NumberedWindowConstructorArgumentComputabilityTargets
open NumberedWindowConstructorStatMarkProof (carrierPath)
open NumberedWindowApplicationDomainProof (annotation)

private theorem literalArgument {S K Γ hk q τ} (h : InWindow S K (finiteC Γ) τ q)
    (hc : ComputableClass S K Γ hk τ (classOf ⟨q, h⟩)) : ComputableArgument S K Γ hk q := by
  unfold ComputableArgument
  rw [annotation h.1]
  exact ⟨h, hc⟩

theorem primitive : PrimitiveReplacementComputableArguments := by
  intro S K Γ hk source target hSource hStep q hq
  obtain ⟨kept, removed, added, pSource, pTarget, _, hOrigins⟩ := hStep
  rcases List.mem_append.mp (pTarget.mem_iff.mp hq) with hKept | hAdded
  · exact hSource q (pSource.mem_iff.mpr (List.mem_append_left _ hKept))
  · obtain ⟨origin, ho, hm⟩ := hOrigins q hAdded
    obtain ⟨hWindow, hComputable⟩ := hSource origin (pSource.mem_iff.mpr (List.mem_append_right _ ho))
    obtain ⟨hr, hPath⟩ := carrierPath hk hWindow hm
    exact literalArgument hr (exact_ComputablePositiveDescendants S K Γ origin.type hk _ _ hPath hComputable)

theorem raw : RawStepComputableArgument := by
  intro S K Γ hk q r hSource hrTyped hStep
  obtain ⟨hq, hComputable⟩ := hSource
  obtain ⟨hSameType, hrGuard⟩ := NumberedWindowPreservationRawProof.rawGuard hk hStep _ hq
  let hr : InWindow S K (finiteC Γ) q.type r := ⟨hSameType ▸ hrTyped, hrGuard⟩
  let Q : WindowCarrier S K (finiteC Γ) q.type := ⟨q, hq⟩
  let R : WindowCarrier S K (finiteC Γ) q.type := ⟨r, hr⟩
  have hEdge : ClassEdge (classOf Q) (classOf R) := ⟨Q, R, rfl, rfl, hStep⟩
  exact literalArgument hr (exact_ComputableDirectDescendants S K Γ q.type hk _ _ hEdge hComputable)

private theorem listStep {S K Γ} (hk : DecisionSourceUniverse.Closed K)
    (source target : NArgs) (h : RawArgsStep S K source target) :
    (∀ q ∈ source.toList, ComputableArgument S K Γ hk q) →
    (∀ r ∈ target.toList, Typed (finiteC Γ) r r.type) →
    ∀ r ∈ target.toList, ComputableArgument S K Γ hk r := by
  cases source with
  | nil => cases h
  | cons q rest =>
    cases h with
    | first hStep =>
      intro hSource hTyped r hr
      rcases List.mem_cons.mp hr with rfl | hTail
      · exact raw S K Γ hk q _ (hSource q List.mem_cons_self) (hTyped _ List.mem_cons_self) hStep
      · exact hSource r (List.mem_cons_of_mem _ hTail)
    | later hStep =>
      intro hSource hTyped r hr
      rcases List.mem_cons.mp hr with rfl | hTail
      · exact hSource _ List.mem_cons_self
      · exact listStep hk rest _ hStep
          (fun x hx => hSource x (List.mem_cons_of_mem _ hx))
          (fun x hx => hTyped x (List.mem_cons_of_mem _ hx)) r hTail
termination_by sizeOf source

theorem arguments : RawArgsStepComputableArguments := by
  intro S K Γ hk source target hSource hTyped hStep
  exact listStep hk source target hStep hSource hTyped

end LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityProof
