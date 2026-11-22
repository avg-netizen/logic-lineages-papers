module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowTargets
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowLocalityProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates dimension strips exactBitFamilyLowStrips exactBitFamilyLowDimension)

theorem exactBitFamilyExistentialLow : ExactBitFamilyExistentialLow := by
  intro f bound family
  constructor
  · rintro ⟨ρ,⟨name,used,below⟩,truth⟩
    let a := ρ name
    have stable : Function.update ρ name a = ρ := Function.update_eq_self _ _
    have source := (exactBitFamilyLowStrips f ρ name bound family (fun _ => True)).mp
      ⟨a,below,True.intro,by rw [stable]; exact truth⟩
    obtain ⟨branch,member,_,child⟩ := source
    have out : branch.2 ∈ children f bound family :=
      List.mem_flatMap.mpr ⟨name,Finset.mem_toList.mpr used,List.mem_map.mpr ⟨branch,member,rfl⟩⟩
    exact ⟨branch.2,out,Function.update ρ name branch.1,child⟩
  · rintro ⟨out,member,ρ,truth⟩
    obtain ⟨name,used,fromName⟩ := List.mem_flatMap.mp member
    obtain ⟨branch,inStrips,rfl⟩ := List.mem_map.mp fromName
    have starts := exactBitFamilyLowDimension f name bound family (Finset.mem_toList.mp used) branch inStrips
    let θ := Function.update ρ name branch.1
    have agree (k : Nat) (seen : k ∈ coordinates branch.2) : ρ k = θ k := by
      have ne := (Finset.mem_erase.mp (starts.1 seen)).1
      change ρ k = Function.update ρ name branch.1 k
      rw [Function.update_of_ne ne]
    have retained := (exactBitFamilySupportLocality f ρ θ branch.2 agree).mp truth
    obtain ⟨a,below,_,old⟩ := (exactBitFamilyLowStrips f ρ name bound family (fun _ => True)).mpr
      ⟨branch,inStrips,True.intro,retained⟩
    exact ⟨Function.update ρ name a,⟨name,Finset.mem_toList.mp used,by simpa only [Function.update_self] using below⟩,old⟩

theorem exactBitFamilyExistentialLowDimension : ExactBitFamilyExistentialLowDimension := by
  intro f bound family out member
  obtain ⟨name,used,fromName⟩ := List.mem_flatMap.mp member
  obtain ⟨branch,inStrips,rfl⟩ := List.mem_map.mp fromName
  exact (exactBitFamilyLowDimension f name bound family (Finset.mem_toList.mp used) branch inStrips).2

end LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
