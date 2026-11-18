import LogicLineages.PersistentMarking.ProtectedSpineInterpretationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineTableProof
open Spine DecisionPorts FiniteDomainSchema FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineInterpreter ProtectedSpineLaws
open MarkedConstructorTargets (PrefixClosed)

theorem restrictIdentity (E : Environment) (Γ : Context) (a : Assignments) (ha : InputValid E Γ a) :
    a.restrict E Γ Γ = a := by
  rcases a with ⟨free,bound⟩
  have hf : weakenFree E Γ Γ free = free := by
    conv => rhs; rw [← List.map_id free]
    apply List.map_congr_left
    intro p hp
    have he := (HereditaryRestrictionAlgebraProof.algebra E p.1.1).1 Γ p.2 ha.1 (ha.2.1 p hp)
    simp only [id,he]
  have hb : weakenBound E Γ Γ bound = bound := by
    conv => rhs; rw [← List.map_id bound]
    apply List.map_congr_left
    intro p hp
    have he := (HereditaryRestrictionAlgebraProof.algebra E p.1).1 Γ p.2 ha.1 (ha.2.2 p hp)
    simp only [id,he]
  change (⟨weakenFree E Γ Γ free,weakenBound E Γ Γ bound⟩ : Assignments) = ⟨free,bound⟩
  rw [hf,hb]

theorem table (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (C : BoundContext) (q : Expr) (σ : Ty) (hc : PrefixClosed E)
    (hm : M ∈ MarkedFamilyCoherence.retained E H) (ht : Typed C q σ) (hq : Covered E H q)
    (Γ : Context) (a : Assignments) (ha : InputValid E Γ a)
    (ds : List Ty) (τ : Ty) (xs : List Code) (hpre : (ds,τ) ∈ fullPrefixes σ) (hx : TupleValues E Γ ds xs) :
    nonemptyAt E (evaluate S E H M q) Γ a 0 ds τ xs =
      (valueAt (evaluate S E H M q) Γ a).application Γ ds τ xs := by
  cases q with
  | free α x =>
    cases ht
    exact ProtectedSpineVariableProof.callEq E _ (fun Δ b => freeCode E Δ b.free _ x)
      (fun _ => false) Γ a 0 ds τ xs hpre hx
  | bound α i =>
    cases ht
    have h := ProtectedSpineVariableProof.callEq E σ (fun Δ b => boundCode E Δ b.bound σ i)
      (fun k => protectedLookup k i) Γ a 0 ds τ xs hpre hx
    simpa [protectedLookup] using h
  | lam α body =>
    let ev := evaluate S E H M body
    change nonemptyAt E (ProtectedSpineLambdaCallProof.lambdaEvaluation E α body.type ev) Γ a 0 ds τ xs =
      (valueAt (ProtectedSpineLambdaCallProof.lambdaEvaluation E α body.type ev) Γ a).application Γ ds τ xs
    rw [ProtectedSpineLambdaProof.applicationEq,restrictIdentity E Γ a ha]
  | head f bs =>
    cases ht with
    | head ht =>
      have hbase := ProtectedSpineInterpretationProof.baseLaws S E H M hc hm C bs f.arguments ht
        (ProtectedSpineCoverageProof.ordinaryBase E H f bs hq)
      have hresult := hq.1 f.result (MarkedConstructorSourceTupleProof.rootSupport (.head f bs))
      have hp := ProtectedSpineHeadParameterProof.valid E H f f.result (evaluateArgs S E H M bs)
        (fun _ _ _ => []) [] hbase (ProtectedSpineArgumentProof.nil E) (hq.2 f List.mem_cons_self)
        hresult (by simp) Γ a ha
      exact ProtectedSpineHeadProof.applyEq false S E H M f f.result (evaluateArgs S E H M bs)
        (fun _ _ _ => []) Γ a 0 ds τ xs hp hpre hx
  | marked f υ bs es =>
    cases ht with
    | marked hbs hes =>
      have hbase := ProtectedSpineInterpretationProof.baseLaws S E H M hc hm C bs f.arguments hbs
        (ProtectedSpineCoverageProof.markedBase E H f σ bs es hq)
      have hcov := ProtectedSpineCoverageProof.markedExtras E H f σ bs es hq
      have hExtra := ProtectedSpineInterpretationProof.extraLaws S E H M hc hm C es hes hcov
      have hresult := hq.1 σ (MarkedConstructorSourceTupleProof.rootSupport (.marked f σ bs es))
      have hp := ProtectedSpineHeadParameterProof.valid E H f σ (evaluateArgs S E H M bs)
        (evaluateArgs S E H M es) _ hbase hExtra (hq.2 f List.mem_cons_self)
        hresult (ProtectedSpineCoverageProof.argumentTypes E H es hcov) Γ a ha
      exact ProtectedSpineHeadProof.applyEq true S E H M f σ (evaluateArgs S E H M bs)
        (evaluateArgs S E H M es) Γ a 0 ds τ xs hp hpre hx

end LogicLineages.PersistentMarking.ProtectedSpineTableProof
