import LogicLineages.PersistentMarking.MarkedConstructorAppendProof

namespace LogicLineages.PersistentMarking.MarkedConstructorValidityProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)
open MarkedConstructorAppendProof

theorem inputReflexive (E : Environment) (heads : List Head) (p : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) : InputLE E p p := by
  refine ⟨rfl, rfl, rfl, ?_, fun _ ha => ha⟩
  intro i ρ a b hρ ha hb
  cases ha.symm.trans hb
  exact (HereditaryPartialOrderProof.partialOrder E ρ p.2.2.1 hp.2.2.1).1 a
    (hp.2.2.2.1.2 i ρ a hρ ha)

theorem tablesMonotone (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p q : Parameter) (Δ : Context) (ds : List Ty) (τ : Ty) (xs ys : List Code)
    (hpfx : MarkedConstructorTargets.PrefixClosed E)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hpq : InputLE E p q) (hd : WellFormed E.types E.ports Δ) (he : Extends p.2.2.1 Δ)
    (hpre : (ds,τ) ∈ fullPrefixes p.2.1)
    (hx : TupleValues E Δ ds xs) (hy : TupleValues E Δ ds ys) (hxy : ValuesLE E Δ ds xs ys) :
    (descriptor E τ).le Δ (MarkedConstructorValue.build S E heads M p |>.application Δ ds τ xs)
      (MarkedConstructorValue.build S E heads M q |>.application Δ ds τ ys) = true := by
  have heq : Extends q.2.2.1 Δ := hpq.2.2.1 ▸ he
  have hpreq : (ds,τ) ∈ fullPrefixes q.2.1 := hpq.2.1 ▸ hpre
  have hwp := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hd he
  have hwq := MarkedFamilyCoherenceFoundationProof.destinationValid E heads q Δ hq hd heq
  obtain ⟨a,ha,_,hA⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M p Δ ds τ xs hpfx hm hp hd he hpre hx
  obtain ⟨b,hb,_,hB⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M q Δ ds τ ys hpfx hm hq hd heq hpreq hy
  have ht := hpfx p.2.1 hp.2.1 ds τ hpre
  have hpa := appendValid E heads (weakenParameter E p Δ) τ ds xs hwp ht.1 ht.2 hx
  have hqb := appendValid E heads (weakenParameter E q Δ) τ ds ys hwq ht.1 ht.2 hy
  have hle := appendMonotone E heads (weakenParameter E p Δ) (weakenParameter E q Δ)
    τ ds xs ys hwp hwq (MarkedConstructorParameterProof.weakenMonotone E heads p q Δ hp hq hpq hd he)
    ht.2 hx hy hxy
  rw [hA,hB]
  exact (StructuralMarkedActionProof.laws E heads M hm).1 _ _ a b hpa hqb hle ha hb

theorem tablesNatural (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (p : Parameter) (Δ Θ : Context) (ds : List Ty) (τ : Ty) (xs : List Code)
    (hpfx : MarkedConstructorTargets.PrefixClosed E)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads) (hp : MarkedFamilyParameters.Valid E heads p)
    (hd : WellFormed E.types E.ports Δ) (ht : WellFormed E.types E.ports Θ)
    (he : Extends p.2.2.1 Δ) (hf : Extends Δ Θ)
    (hpre : (ds,τ) ∈ fullPrefixes p.2.1) (hx : TupleValues E Δ ds xs) :
    (descriptor E τ).restrict Δ Θ
        ((MarkedConstructorValue.build S E heads M p).application Δ ds τ xs) =
      (MarkedConstructorValue.build S E heads M p).application Θ ds τ (restrictValues E Δ Θ ds xs) := by
  have heΘ := DecisionPortsProof.extensionTrans _ _ _ he hf
  have hr : TupleValues E Θ ds (restrictValues E Δ Θ ds xs) :=
    MarkedBaseTupleRestrictionProof.restriction E Δ Θ ds xs hd ht hf hx
  have hwp := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hd he
  have htypes := hpfx p.2.1 hp.2.1 ds τ hpre
  let aParam := appendParameter E (weakenParameter E p Δ) τ ds xs
  let bParam := appendParameter E (weakenParameter E p Θ) τ ds (restrictValues E Δ Θ ds xs)
  have hpa : MarkedFamilyParameters.Valid E heads aParam :=
    appendValid E heads (weakenParameter E p Δ) τ ds xs hwp htypes.1 htypes.2 hx
  have hweak : weakenParameter E aParam Θ = bParam := by
    dsimp only [aParam, bParam]
    rw [appendNatural E heads (weakenParameter E p Δ) Θ τ ds xs hwp ht hf htypes.2 hx,
      MarkedConstructorParameterProof.weakenComposition E heads p Δ Θ hp hd ht he hf]
    rfl
  obtain ⟨a,ha,_,hA⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M p Δ ds τ xs hpfx hm hp hd he hpre hx
  obtain ⟨b,hb,_,hB⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M p Θ ds τ
    (restrictValues E Δ Θ ds xs) hpfx hm hp ht heΘ hpre hr
  have hb' : StructuralActions.markedAction E heads M (weakenParameter E aParam Θ) = some b := by
    rw [hweak]
    exact hb
  rw [hA,hB]
  exact (StructuralMarkedActionProof.laws E heads M hm).2 aParam Θ a b hpa ht hf ha hb'

theorem valid : MarkedConstructorTargets.ValueValid := by
  intro S E heads M p hpfx hm hp
  refine ⟨?_, ?_, ?_⟩
  · intro Δ hd he ds τ hpre xs hx
    obtain ⟨a,_,ha,happ⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M p Δ ds τ xs hpfx hm hp hd he hpre hx
    simpa only [happ] using ha
  · intro Δ hd he ds τ hpre xs ys hx hy hxy
    exact tablesMonotone S E heads M p p Δ ds τ xs ys hpfx hm hp hp (inputReflexive E heads p hp)
      hd he hpre hx hy hxy
  · intro Δ Θ hd ht he hf ds τ hpre xs hx
    exact tablesNatural S E heads M p Δ Θ ds τ xs hpfx hm hp hd ht he hf hpre hx

theorem exact_ValueValid : MarkedConstructorTargets.ValueValid := valid
#print axioms exact_ValueValid
end LogicLineages.PersistentMarking.MarkedConstructorValidityProof
