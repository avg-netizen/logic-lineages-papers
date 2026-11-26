module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineEnvironmentWeakeningProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorLiteralProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineEnvironmentLookupProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineEnvironmentTargets

theorem freeEntry (free : FreeValues) (n : Name) (c : Code) (h : lookupFree free n = some c) :
    (n,c) ∈ free := by
  induction free with
  | nil => cases h
  | cons a free ih =>
    obtain ⟨m,v⟩ := a
    by_cases he : m = n
    · subst m
      have hv : v = c := by simpa [lookupFree] using h
      subst v
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookupFree,he] using h))

theorem boundEntry (bound : BoundValues) (σ : Ty) (i : Nat) (c : Code)
    (h : lookupBound bound σ i = some c) : (σ,c) ∈ bound := by
  cases hi : bound[i]? with
  | none => simp [lookupBound,hi] at h
  | some p =>
    obtain ⟨ρ,v⟩ := p
    have hp : ρ = σ ∧ v = c := by
      by_cases he : ρ = σ <;> simp_all [lookupBound]
    obtain ⟨rfl,rfl⟩ := hp
    exact List.mem_of_getElem? hi

theorem freeLookup (E : Environment) (Γ : Context) (free : FreeValues) (σ : Ty) (x : Nat)
    (hw : WellFormed E.types E.ports Γ) (hf : FreeValid E Γ free) :
    freeCode E Γ free σ x ∈ (descriptor E σ).carriers Γ := by
  cases he : lookupFree free (σ,x) with
  | none =>
    simpa [freeCode,he] using MarkedConstructorLiteralProof.literalRetained E Γ σ x hw
  | some c =>
    simpa [freeCode,he] using hf ((σ,x),c) (freeEntry free (σ,x) c he)

theorem boundLookup (E : Environment) (Γ : Context) (bound : BoundValues) (σ : Ty) (i : Nat)
    (hw : WellFormed E.types E.ports Γ) (hb : BoundValid E Γ bound) :
    boundCode E Γ bound σ i ∈ (descriptor E σ).carriers Γ := by
  cases he : lookupBound bound σ i with
  | none =>
    simpa [boundCode,he] using (StructuralWholeBottomProof.wholeBottom E σ Γ hw).1
  | some c =>
    simpa [boundCode,he] using hb (σ,c) (boundEntry bound σ i c he)

theorem lookup : CodeLookup := by
  intro E Γ free bound σ x i hw hf hb
  exact ⟨freeLookup E Γ free σ x hw hf,boundLookup E Γ bound σ i hw hb⟩

theorem exact_CodeLookup : CodeLookup := lookup
#print axioms exact_CodeLookup
end LogicLineages.PersistentMarking.ProtectedSpineEnvironmentLookupProof
