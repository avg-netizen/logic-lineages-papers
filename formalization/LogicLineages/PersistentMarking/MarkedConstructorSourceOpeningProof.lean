import LogicLineages.PersistentMarking.MarkedConstructorSourceTupleProof
import LogicLineages.PersistentMarking.MarkedConstructorCanonicalOpeningProof
import LogicLineages.PersistentMarking.MarkedConstructorLiteralProof
import LogicLineages.PersistentMarking.MarkedConstructorAppendProof

namespace LogicLineages.PersistentMarking.MarkedConstructorSourceOpeningProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics MarkedConstructorOperator
open MarkedFamilyParameters (Parameter)
open ProtectedSpineEnvironment (openingSlot openingContext literalCode)

theorem openingSuccess (S : Signature) (s t : Expr) (σ τ : Ty)
    (hs : PaperTerm S s σ) (ht : PaperTerm S t τ) (hos : Ordinary s) (hot : Ordinary t)
    (M : Code) (p : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained (environment s t) (inventory s t).sourceHeads)
    (hp : MarkedFamilyParameters.Valid (environment s t) (inventory s t).sourceHeads p)
    (α β : Ty) (body : Expr) (h : p.2.1 = .arrow α β)
    (hobs : Expr.lam α body ∈ observations (environment s t).names (environment s t).ports p.2.2.1 t p.2.1) :
    ∃ i c, openingSlot p.2.2.1 = some i ∧
      let E := environment s t
      let Θ := openingContext p.2.2.1 α i
      WellFormed E.types E.ports Θ ∧ Extends p.2.2.1 Θ ∧ used Θ = used p.2.2.1 + 1 ∧
      openBody α (portName E.names i) body ∈ observations E.names E.ports Θ t β ∧
      StructuralActions.markedAction E (inventory s t).sourceHeads M
        (MarkedConstructorTests.fabsParameter E p α β i) = some c ∧
      c ∈ (descriptor E β).carriers Θ := by
  let E := environment s t
  let heads := (inventory s t).sourceHeads
  have hc := MarkedConstructorInventoryProof.prefixClosed s t σ τ hs.1 ht.1 hos hot
  have htypes := hc p.2.1 hp.2.1 [α] β (by rw [h]; exact List.mem_cons_self)
  have hα := htypes.2 α List.mem_cons_self
  rw [h] at hobs
  obtain ⟨i,hi,hΔ,he,hused,hopen⟩ :=
    ObservationLambdaProof.descent S E.types E.names E.ports p.2.2.1 t τ α β body ht hot hp.2.2.1 hα hobs
  have hcontext := MarkedConstructorCanonicalOpeningProof.openingEqFill p.2.2.1 α i
  let Θ := openingContext p.2.2.1 α i
  have hw : WellFormed E.types E.ports Θ := by
    dsimp only [Θ]
    rw [hcontext]
    exact hΔ
  have hExtends : Extends p.2.2.1 Θ := by dsimp only [Θ]; rw [hcontext]; exact he
  let v := literalCode E Θ α (portName E.names i)
  have hv := MarkedConstructorLiteralProof.literalRetained E Θ α (portName E.names i) hw
  have htuple : TupleValues E Θ [α] [v] :=
    (HereditaryTupleProof.tupleCons E Θ α [] v []).mpr ⟨hv,HereditaryTupleProof.tupleNil E Θ⟩
  have hwp := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Θ hp hw hExtends
  have hparam : MarkedFamilyParameters.Valid E heads (MarkedConstructorTests.fabsParameter E p α β i) :=
    MarkedConstructorAppendProof.appendValid E heads (MarkedFamilyCoherence.weakenParameter E p Θ)
      β [α] [v] hwp htypes.1 htypes.2 htuple
  obtain ⟨c,hc,hcm⟩ := StructuralMarkedActionProof.sound E heads M _ hm hparam
  refine ⟨i,c,MarkedConstructorCanonicalOpeningProof.slotEq p.2.2.1 i hi,hw,hExtends,?_,?_,hc,hcm⟩
  · rw [hcontext]
    exact hused
  · rw [hcontext]
    exact hopen

end LogicLineages.PersistentMarking.MarkedConstructorSourceOpeningProof
