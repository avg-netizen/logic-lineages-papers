module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOwnerOrderProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOpeningProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorLiteralProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorAppendProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorFAbsOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)
open MarkedConstructorTargets (FAbsWitness PrefixClosed)
open MarkedConstructorAppendProof
open ProtectedSpineEnvironment (openingContext openingSlot literalCode)

theorem familyOrder (E : Environment) (heads : List Head) (M N : Code) (p : Parameter) (t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hn : N ∈ MarkedFamilyCoherence.retained E heads) (hmn : MarkedFamilyLattice.le E heads M N = true)
    (h : FAbsWitness E heads M p t) : FAbsWitness E heads N p t := by
  obtain ⟨σ,τ,body,i,a,ht,hterm,hi,ha,hbit⟩ := h
  let q := MarkedConstructorTests.fabsParameter E p σ τ i
  have hq := MarkedConstructorLookupProof.actionValid E heads M q a ha
  obtain ⟨b,hb,hbc,hle⟩ := MarkedConstructorLookupProof.actionOrder E heads M N q a hm hn hmn ha
  refine ⟨σ,τ,body,i,b,ht,hterm,hi,hb,?_⟩
  exact MarkedConstructorBitOrderProof.decodeMonotone false E τ q.2.2.1
    a b (openBody σ (portName E.names i) body) hq.1.2.2.1 hq.2 hbc hle hbit

theorem inputOrder (E : Environment) (heads : List Head) (M : Code) (p q : Parameter) (t : Expr)
    (hpfx : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hpq : InputLE E p q) (h : FAbsWitness E heads M p t) :
    FAbsWitness E heads M q t := by
  obtain ⟨σ,τ,body,i,a,ht,hterm,hi,ha,hbit⟩ := h
  have htq := hpq.2.1.symm.trans ht
  have hpΓq := hpq.2.2.1
  have hiq : openingSlot q.2.2.1 = some i := hpΓq ▸ hi
  have htypes := hpfx p.2.1 hp.2.1 [σ] τ (by rw [ht]; exact List.mem_cons_self)
  have hσ := htypes.2 σ List.mem_cons_self
  let Θ := openingContext p.2.2.1 σ i
  have heq : openingContext q.2.2.1 σ i = Θ := congrArg (fun Γ => openingContext Γ σ i) hpΓq.symm
  have hnone := MarkedConstructorOpeningProof.slotUnused p.2.2.1 i hi
  have hw : WellFormed E.types E.ports Θ :=
    MarkedConstructorOpeningProof.openingWellFormed E.types E.ports p.2.2.1 σ i hp.2.2.1 hσ hnone
  have he : Extends p.2.2.1 Θ := MarkedConstructorOpeningProof.openingExtends p.2.2.1 σ i hnone
  have he' : Extends q.2.2.1 Θ := hpΓq ▸ he
  have hwp := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Θ hp hw he
  have hwq := MarkedFamilyCoherenceFoundationProof.destinationValid E heads q Θ hq hw he'
  let v := literalCode E Θ σ (portName E.names i)
  have hv := MarkedConstructorLiteralProof.literalRetained E Θ σ (portName E.names i) hw
  have hvTuple : TupleValues E Θ [σ] [v] :=
    (HereditaryTupleProof.tupleCons E Θ σ [] v []).mpr ⟨hv,HereditaryTupleProof.tupleNil E Θ⟩
  have hvOrder : ValuesLE E Θ [σ] [v] [v] :=
    (MarkedBaseTupleFoundationProof.valuesCons E Θ σ [] v v [] []).mpr
      ⟨(HereditaryPartialOrderProof.partialOrder E σ Θ hw).1 v hv,
        fun i ρ a b h _ _ => by cases i <;> cases h⟩
  let left := appendParameter E (weakenParameter E p Θ) τ [σ] [v]
  let right := appendParameter E (weakenParameter E q Θ) τ [σ] [v]
  have hright : MarkedFamilyParameters.Valid E heads right :=
    appendValid E heads (weakenParameter E q Θ) τ [σ] [v] hwq htypes.1 htypes.2 hvTuple
  have hle : InputLE E left right :=
    appendMonotone E heads (weakenParameter E p Θ) (weakenParameter E q Θ) τ [σ] [v] [v]
      hwp hwq (MarkedConstructorParameterProof.weakenMonotone E heads p q Θ hp hq hpq hw he)
      htypes.2 hvTuple hvTuple hvOrder
  obtain ⟨b,hb,hbc,hab⟩ := MarkedConstructorLookupProof.actionInputOrder E heads M left right a hm hright hle ha
  have hac := (MarkedConstructorLookupProof.actionValid E heads M left a ha).2
  refine ⟨σ,τ,body,i,b,htq,hterm,hiq,?_,?_⟩
  · unfold MarkedConstructorTests.fabsParameter
    rw [heq]
    exact hb
  · rw [heq]
    exact MarkedConstructorBitOrderProof.decodeMonotone false E τ Θ
      a b (openBody σ (portName E.names i) body) hw hac hbc hab hbit

end LogicLineages.PersistentMarking.MarkedConstructorFAbsOrderProof
