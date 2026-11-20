import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalMultisetClosureChecks

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticLeastClassChecks NumberedWindowArithmeticClassAddress
open NumberedWindowExternalIDOperators NumberedWindowExternalTypeFactsChecks
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorArgumentAddressTargets

theorem primary : PrimaryArgumentAddress := by
  intro S K Γ τ q r hk hq hr equiv
  unfold slot
  rw [NumberedWindowApplicationDomainProof.annotation hq.1, NumberedWindowApplicationDomainProof.annotation hr.1]
  rw [(exact_LeastCodeReflectsPrimary S K Γ τ q r hk hq hr).mpr equiv]

theorem permuted : PermutedArgumentAddresses := by
  intro S K Γ xs ys cs ds p hx hy
  have hp := p.map (slot S K Γ)
  rw [show xs.toList.map (slot S K Γ) = cs.map some from hx,
    show ys.toList.map (slot S K Γ) = ds.map some from hy] at hp
  have back := hp.map (fun n : Option Nat => n.getD 0)
  simpa [List.map_map, Function.comp_def] using back

private theorem single {S K Γ hk q} (h : ComputableArgument S K Γ hk q) :
    ∃ c, slot S K Γ q = some c ∧ Least (scalarStep S K) c := by
  obtain ⟨hq,hc⟩ := h
  obtain ⟨i,rep,hi,_,_,_,_,_,_⟩ := exact_LeastCodeSpecification S K Γ q.type q hk hq
  refine ⟨encodeAddress ⟨Γ,q.type,i⟩,by simp only [slot,hi,Option.map_some],?_⟩
  exact exact_ComputabilityImpliesScalarI S K Γ q.type hk (classOf ⟨q,hq⟩) i ⟨⟨q,hq⟩,rfl,hi⟩ hc

private theorem collect {S K Γ hk} (qs : List NTerm) (h : ∀ q ∈ qs, ComputableArgument S K Γ hk q) :
    ∃ cs, qs.map (slot S K Γ) = cs.map some ∧ ∀ c ∈ cs, Least (scalarStep S K) c := by
  induction qs with
  | nil => exact ⟨[],rfl,by intro c hc; cases hc⟩
  | cons q qs ih =>
    obtain ⟨c,hc,ac⟩ := single (h q (List.mem_cons_self ..))
    obtain ⟨cs,hs,as⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨c::cs,by simp only [List.map_cons,hc,hs],?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hp
    · exact ac
    · exact as x hp

theorem multiset : ComputableArgumentsGiveMultiset := by
  intro S K Γ hk xs h
  obtain ⟨cs,hc,hs⟩ := collect xs.toList h
  exact ⟨cs,hc,hs,NumberedWindowExternalMultisetClosureChecks.exact_ExternalIFiniteMultiset S K cs hs⟩

end LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressProof
