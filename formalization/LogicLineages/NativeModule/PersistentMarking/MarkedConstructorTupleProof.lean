module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets
public import LogicLineages.NativeModule.PersistentMarking.StructuralMarkedActionProof
public import LogicLineages.NativeModule.PersistentMarking.StructuralExtraInsertionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorTupleProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open MarkedConstructorTargets

theorem prefixResidual {σ τ : Ty} {ds : List Ty} (h : (ds,τ) ∈ fullPrefixes σ) :
    ProtectedSpineEnvironment.residualType σ ds = some τ := by
  induction σ generalizing ds τ with
  | ground => simp [fullPrefixes] at h
  | arrow ρ υ ihr ihu =>
    simp only [fullPrefixes,List.mem_cons,List.mem_map] at h
    rcases h with h | ⟨p,hp,he⟩
    · cases h; simp [ProtectedSpineEnvironment.residualType]
    · cases he
      simpa [ProtectedSpineEnvironment.residualType] using ihu hp

theorem tupleTags (E : Environment) (Γ : Context) (ds : List Ty)
    (xs : List FiniteDomainSchema.Code) (ht : ∀ ρ, ρ ∈ ds → ρ ∈ E.types)
    (hx : TupleValues E Γ ds xs) :
    ∀ a, a ∈ ds.zip xs → a ∈ MarkedExtras.«universe» E Γ := by
  induction ds generalizing xs with
  | nil => simp
  | cons ρ ds ih =>
    cases xs with
    | nil => have h := hx.1; simp at h
    | cons x xs =>
      have hc := (HereditaryTupleProof.tupleCons E Γ ρ ds x xs).mp hx
      intro a ha
      simp only [List.zip_cons_cons,List.mem_cons] at ha
      rcases ha with ha | ha
      · subst a
        exact (MarkedExtrasFoundationProof.universeExact E Γ ρ x).mpr
          ⟨ht ρ (List.mem_cons_self),hc.1⟩
      · exact ih xs (fun σ hs => ht σ (List.mem_cons_of_mem _ hs)) hc.2 a ha

theorem tupleSuccess : MarkedConstructorTargets.TupleSuccess := by
  intro S E heads M p Δ ds τ xs hpfx hm hp hd he hpre hxs
  have hw := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hd he
  have htypes := hpfx p.2.1 hp.2.1 ds τ hpre
  have hins := StructuralExtraInsertionProof.valid E Δ
    (MarkedFamilyCoherence.weakenParameter E p Δ).2.2.2.2 (ds.zip xs) hd hw.2.2.2.2
    (tupleTags E Δ ds xs htypes.2 hxs)
  have hq : MarkedFamilyParameters.Valid E heads
      (p.1,τ,Δ,(MarkedFamilyCoherence.weakenParameter E p Δ).2.2.2.1,
       StructuralActions.insertExtras E Δ (MarkedFamilyCoherence.weakenParameter E p Δ).2.2.2.2 (ds.zip xs)) :=
    ⟨hp.1,htypes.1,hd,hw.2.2.2.1,hins⟩
  obtain ⟨c,hc,hcm⟩ := StructuralMarkedActionProof.sound E heads M _ hm hq
  refine ⟨c,hc,hcm,?_⟩
  simp [MarkedConstructorValue.build,ProtectedSpineEnvironment.originalHeadCall,
    prefixResidual hpre,hxs.1,hc]
end LogicLineages.PersistentMarking.MarkedConstructorTupleProof
