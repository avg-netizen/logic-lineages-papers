module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseSourceProof
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof
public import LogicLineages.OrdinalComparison.WWGroundTupleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProof
open RecursorFreeVector Source Source.ForwardTranslation CommonLayerSyntax

private theorem compiled_scalar {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c) :
    compileScalar (v 0) = some c.scalar := by
  obtain ⟨s,hs,p,hp,he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, AdmissibleAssignment.collect n (fun j => extractPositive (v j.succ)) = some p ∧
        CompiledVector.mk s p = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
  subst c
  exact hs

private theorem original_compilation (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (τ : Ty) (e : OriginalTerm Γ τ) (hf : SourceClasses.recursorFree e = true) :
    ∃ (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level) (t : BaseTerm),
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy e = some v ∧
      compileVector v = some c ∧ FiniteCoefficientBase.compile FiniteCoefficientBase.rawIndex c.scalar = some t := by
  obtain ⟨v,hv,c,hc,_⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy e
  obtain ⟨w,s,t,hw,hs,ht,_⟩ := FiniteCoefficientBaseProof.actualRecursorFreeSource Γ hΓ τ e hf
  have he : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  have hsc : s = c.scalar := Option.some.inj (hs.symm.trans (compiled_scalar v c hc))
  subst s
  exact ⟨v,c,t,hv,hc,ht⟩

theorem actualRecursorFreeDecision : RecursorFreeVectorTargets.ActualRecursorFreeDecision := by
  intro Γ hΓ τ a b ha hb mode
  obtain ⟨av,ac,ta,hav,hac,hta⟩ := original_compilation Γ hΓ τ a ha
  obtain ⟨bv,bc,tb,hbv,hbc,htb⟩ := original_compilation Γ hΓ τ b hb
  obtain ⟨answer,hanswer,hsem⟩ := actualVectorDecision (OrdinalComponent Γ) FiniteCoefficientBase.rawIndex
    Γ.length mode τ.level τ.level ac bc ta tb hta htb
  refine ⟨av,bv,hav,hbv,answer,?_,?_⟩
  · unfold Code.decideSource
    rw [GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ a av ac hav hac,
      GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ b bv bc hbv hbc]
    exact hanswer
  · rw [← hsem]
    constructor
    · intro h ν hp
      apply (actualSourceRelation Γ τ.level τ.level mode av bv ac bc hac hbc _).mpr
      apply h
      intro c
      exact hp (FiniteCoefficientBase.rawIndex c)
        (SourceTypedPortsProof.typedVariableIndex.1 Γ c.1 c.2.1)
    · intro h ρ hp
      obtain ⟨xs,hlen,hxs⟩ := groundPositiveTupleComplete Γ hΓ ρ hp
      have hs := h (fun i => xs.getD i 0 + 1) (fun i hi => Nat.zero_lt_succ _)
      have he : (fun c : OrdinalComponent Γ => xs.getD (FiniteCoefficientBase.rawIndex c) 0 + 1) = ρ :=
        funext hxs
      rw [he] at hs
      exact (actualSourceRelation Γ τ.level τ.level mode av bv ac bc hac hbc ρ).mp hs
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProof
