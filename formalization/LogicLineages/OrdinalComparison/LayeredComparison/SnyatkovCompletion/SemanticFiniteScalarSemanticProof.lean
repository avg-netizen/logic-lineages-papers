module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProof
open SemanticFiniteScalar Source Source.ForwardTranslation CommonLayerSyntax

theorem actualScalar : SemanticFiniteScalarTargets.ActualScalar := by
  intro ι index s
  induction s with
  | one => intro t ht; cases Option.some.inj ht; exact ⟨fun _ => rfl, rfl⟩
  | var i => intro t ht; cases Option.some.inj ht; exact ⟨fun _ => rfl, rfl⟩
  | add a b iha ihb =>
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x, compile index a = some x ∧ ∃ y, compile index b = some y ∧ BaseTerm.add x y=t := by
      simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    obtain ⟨hxv, hxs⟩ := iha x hx
    obtain ⟨hyv, hys⟩ := ihb y hy
    exact ⟨fun ν => congrArg₂ Nat.add (hxv ν) (hyv ν), by simp only [BaseTerm.variables, FiniteCoefficientBase.support, hxs, hys]⟩
  | shift c a ih =>
    intro t ht
    obtain ⟨k, hk, x, hx, rfl⟩ : ∃ k, SemanticCoefficient.Code.recognize (closedPositiveCode c) = some k ∧ ∃ x, compile index a = some x ∧ FiniteCoefficientBase.expand k x=t := by
      simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    obtain ⟨hxv, hxs⟩ := ih x hx
    refine ⟨?_, (FiniteCoefficientBaseProof.exactExpansion k x).2.trans hxs⟩
    intro ν
    rw [(FiniteCoefficientBaseProof.exactExpansion k x).1 ν, hxv ν]
    change actualCollapse _ = actualCollapse (ordinalNaturalProduct Ordinal.omega0 c.evaluate.1.repr + _)
    rw [(SemanticCoefficientProof.exactNaturalValue c k).mp hk, Source.ParametricFiniteCollapseArgument.Proof.naturalProduct_omega_finite]


theorem exactSuccessClass : SemanticFiniteScalarTargets.ExactSuccessClass := by
  intro ι index s
  induction s with
  | one => exact ⟨fun _ => trivial, fun _ => ⟨.numeral 1,rfl⟩⟩
  | var i => exact ⟨fun _ => trivial, fun _ => ⟨.variable (index i),rfl⟩⟩
  | add a b iha ihb =>
    constructor
    · rintro ⟨t,ht⟩
      obtain ⟨x,hx,y,hy,_⟩ : ∃ x, compile index a = some x ∧ ∃ y, compile index b = some y ∧ BaseTerm.add x y=t := by
        simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
      exact ⟨iha.mp ⟨x,hx⟩,ihb.mp ⟨y,hy⟩⟩
    · rintro ⟨ha,hb⟩
      obtain ⟨x,hx⟩ := iha.mpr ha
      obtain ⟨y,hy⟩ := ihb.mpr hb
      exact ⟨.add x y,by simp [compile,hx,hy]⟩
  | shift c a ih =>
    constructor
    · rintro ⟨t,ht⟩
      obtain ⟨k,hk,x,hx,_⟩ : ∃ k, SemanticCoefficient.Code.recognize (closedPositiveCode c) = some k ∧
          ∃ x, compile index a = some x ∧ FiniteCoefficientBase.expand k x=t := by
        simpa only [compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
      exact ⟨(SemanticCoefficientProof.exactFiniteAcceptance c).mp ⟨k,hk⟩,ih.mp ⟨x,hx⟩⟩
    · rintro ⟨hc,ha⟩
      obtain ⟨k,hk⟩ := (SemanticCoefficientProof.exactFiniteAcceptance c).mpr hc
      obtain ⟨x,hx⟩ := ih.mpr ha
      exact ⟨FiniteCoefficientBase.expand k x,by simp [compile,hk,hx]⟩

theorem structuralExtension : SemanticFiniteScalarTargets.StructuralExtension := by
  intro ι index s
  induction s with
  | one => intro t ht; cases Option.some.inj ht; rfl
  | var i => intro t ht; cases Option.some.inj ht; rfl
  | add a b iha ihb =>
    intro t ht
    obtain ⟨x,hx,y,hy,rfl⟩ : ∃ x, FiniteCoefficientBase.compile index a = some x ∧
        ∃ y, FiniteCoefficientBase.compile index b = some y ∧ BaseTerm.add x y=t := by
      simpa only [FiniteCoefficientBase.compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    simp [compile,iha x hx,ihb y hy]
  | shift c a ih =>
    intro t ht
    obtain ⟨k,hk,x,hx,rfl⟩ : ∃ k, FiniteCoefficientBase.coefficient c = some k ∧
        ∃ x, FiniteCoefficientBase.compile index a = some x ∧ FiniteCoefficientBase.expand k x=t := by
      simpa only [FiniteCoefficientBase.compile, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using ht
    simp [compile,SemanticCoefficientProof.structuralExtension c k hk,ih x hx]
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProof
