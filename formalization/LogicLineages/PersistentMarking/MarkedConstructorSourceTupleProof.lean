import LogicLineages.PersistentMarking.MarkedConstructorSourceLookupTargets
import LogicLineages.PersistentMarking.MarkedConstructorSelectOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorInventoryProof
import LogicLineages.PersistentMarking.DecisionObservedTypesProof
import LogicLineages.PersistentMarking.MarkedBaseHeadCoverageProof

namespace LogicLineages.PersistentMarking.MarkedConstructorSourceTupleProof
open Spine DecisionInventory DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics MarkedConstructorOperator
open MarkedFamilyParameters (Parameter)

theorem ownerSuccess (E : Environment) (heads : List Head) (M : Code) (p : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads) (hp : MarkedFamilyParameters.Valid E heads p)
    (σ : Ty) (hσ : σ ∈ E.types) :
    ∃ c, MarkedConstructorTests.owner E heads M p σ = some c ∧ c ∈ (descriptor E σ).carriers p.2.2.1 :=
  StructuralMarkedActionProof.sound E heads M (p.1, σ, p.2.2.1, p.2.2.2.1, p.2.2.2.2) hm
    ⟨hp.1,hσ,hp.2.2⟩

theorem ownerTupleSuccess (E : Environment) (heads : List Head) (M : Code) (p : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads) (hp : MarkedFamilyParameters.Valid E heads p)
    (ds : List Ty) (ht : ∀ σ, σ ∈ ds → σ ∈ E.types) :
    ∃ cs, MarkedConstructorTests.ownerTuple E heads M p ds = some cs ∧ TupleValues E p.2.2.1 ds cs := by
  induction ds with
  | nil => exact ⟨[],rfl,HereditaryTupleProof.tupleNil E _⟩
  | cons σ ds ih =>
    obtain ⟨c,hc,hcm⟩ := ownerSuccess E heads M p hm hp σ (ht σ List.mem_cons_self)
    obtain ⟨cs,hcs,hvs⟩ := ih (fun ρ hρ => ht ρ (List.mem_cons_of_mem _ hρ))
    refine ⟨c::cs, ?_, (HereditaryTupleProof.tupleCons E _ σ ds c cs).mpr ⟨hcm,hvs⟩⟩
    change ds.mapM (MarkedConstructorTests.owner E heads M p) = some cs at hcs
    simp [MarkedConstructorTests.ownerTuple,List.mapM_cons,hc,hcs]

theorem selectSuccess (S : Signature) (s t : Expr) (σ τ : Ty)
    (hs : PaperTerm S s σ) (ht : PaperTerm S t τ) (hos : Ordinary s) (hot : Ordinary t)
    (M : Code) (p : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained (environment s t) (inventory s t).sourceHeads)
    (hp : MarkedFamilyParameters.Valid (environment s t) (inventory s t).sourceHeads p)
    (a : MarkedExtras.Tagged) (ha : a ∈ MarkedConstructorSelectOrderProof.selectedTags p)
    (ds : List Ty) (υ : Ty) (hpre : (ds,υ) ∈ fullPrefixes a.1) :
    ∃ xs, MarkedConstructorTests.ownerTuple (environment s t) (inventory s t).sourceHeads M p ds = some xs ∧
      TupleValues (environment s t) p.2.2.1 ds xs ∧
      StructuralActions.fullAction (environment s t) a.1 p.2.2.1 a.2 ds υ xs ∈
        (descriptor (environment s t) υ).carriers p.2.2.1 := by
  let E := environment s t
  let heads := (inventory s t).sourceHeads
  have hac := MarkedConstructorSelectOrderProof.tagCarrier E heads p a hp ha
  have htype : a.1 ∈ E.types := by
    rcases List.mem_append.mp ha with hb | he
    · obtain ⟨a',c⟩ := a
      exact (MarkedBaseHeadCoverageProof.coverage s t σ τ hs.1 ht.1 hos hot p.1 hp.1).2
        a' (List.of_mem_zip hb).1
    · have hmem := MarkedExtrasDownProof.canonicalMember E p.2.2.1 p.2.2.2.2 hp.2.2.2.2.1 a he
      exact ((MarkedExtrasFoundationProof.universeExact E p.2.2.1 a.1 a.2).mp hmem).1
  have hc := MarkedConstructorInventoryProof.prefixClosed s t σ τ hs.1 ht.1 hos hot
  obtain ⟨xs,hxs,hv⟩ := ownerTupleSuccess E heads M p hm hp ds (hc a.1 htype ds υ hpre).2
  exact ⟨xs,hxs,hv,StructuralFullActionProof.sound E a.1 p.2.2.1 a.2 ds υ xs hp.2.2.1 hac hpre hv⟩

theorem argumentSupport (ts : Args) (u : Expr) (hu : u ∈ MarkedConstructorTests.terms ts) :
    u.type ∈ auxiliaryArgs ts := by
  induction ts with
  | nil => cases hu
  | cons q ts ih =>
    rw [MarkedConstructorTests.terms,List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact List.mem_append_left _ (DecisionSourceBasicProof.rootType _ _ _ _ _ (fun α hα => hα, by simp, by simp))
    · exact List.mem_append_right _ (ih hu)

end LogicLineages.PersistentMarking.MarkedConstructorSourceTupleProof
