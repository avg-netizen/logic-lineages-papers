module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage

open LogicLineages.OrdinalComparison.Source GroundEquivalence RawSourceDAG

private theorem castVariable {Ξ K : List Ty} {τ : Ty} (h : K = Ξ) (x : Variable Ξ τ) :
    (h.symm ▸ (Term.var x : OriginalTerm Ξ τ) : OriginalTerm K τ) = .var (h.symm ▸ x) := by
  subst Ξ
  rfl

private theorem castApplication {Ξ K : List Ty} {σ τ : Ty} (h : K = Ξ)
    (f : OriginalTerm Ξ (.arrow σ τ)) (a : OriginalTerm Ξ σ) :
    (h.symm ▸ Term.app f a : OriginalTerm K τ) = .app (h.symm ▸ f) (h.symm ▸ a) := by
  subst Ξ
  rfl

private theorem castLambda {Ξ K : List Ty} {σ τ : Ty} (h : K = Ξ)
    (b : OriginalTerm (σ :: Ξ) τ) :
    (h.symm ▸ Term.lam b : OriginalTerm K (.arrow σ τ)) =
      .lam ((congrArg (List.cons σ) h).symm ▸ b) := by
  subst Ξ
  rfl

theorem typedIn {Ξ : List Ty} {τ : Ty} (t : OriginalTerm Ξ τ)
    (Γ Δ : List Ty) (h : Δ ++ Γ = Ξ) {ss : List Spec} (d : DAG Γ ss) :
    let r := buildIn t Γ Δ h d
    r.graph.values (.here : Ref ((Δ,τ) :: r.tail) (Δ,τ)) = (h.symm ▸ t) ∧
    ∀ (s : Spec) (a : Ref ss s), r.graph.values (r.keep a) = d.values a := by
  induction t generalizing Γ Δ ss with
  | var x =>
    rw [castVariable h x]
    simp [buildIn, DAG.values, extendValues]
  | zeroC =>
    cases h
    simp [buildIn, DAG.values, extendValues]
  | succC =>
    cases h
    simp [buildIn, DAG.values, extendValues]
  | caseC σ =>
    cases h
    simp [buildIn, DAG.values, extendValues]
  | recC σ =>
    cases h
    simp [buildIn, DAG.values, extendValues]
  | app f a ihf iha =>
    let F := buildIn f Γ Δ h d
    let A := buildIn a Γ Δ h F.graph
    have hf := ihf Γ Δ h d
    have ha := iha Γ Δ h F.graph
    rw [castApplication h f a]
    simp only [buildIn, DAG.values, extendValues]
    constructor
    · change Term.app (A.graph.values (A.keep .here)) (A.graph.values .here) = _
      rw [ha.2, hf.1, ha.1]
    · intro s r
      change A.graph.values (A.keep (F.keep r)) = _
      rw [ha.2,hf.2]
  | @lam Ξ σ τ b ih =>
    let B := buildIn b Γ (σ :: Δ) (congrArg (List.cons σ) h) d
    have hb := ih Γ (σ :: Δ) (congrArg (List.cons σ) h) d
    rw [castLambda h b]
    simp only [buildIn, DAG.values, extendValues]
    constructor
    · change Term.lam (B.graph.values .here) = _
      exact congrArg (fun z : OriginalTerm ((σ :: Δ) ++ Γ) τ => Term.lam z) hb.1
    · intro s r
      change B.graph.values (B.keep r) = _
      exact hb.2 s r
  | ranked s _ _ => nomatch s

theorem typedBuild : CurrentTreeInputCoverageTargets.ActualTypedBuild := by
  intro Γ Δ τ t ss d
  exact typedIn t Γ Δ rfl d

theorem inputTerm {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) : (input t).term = t :=
  (typedBuild Γ [] τ t [] .nil).1

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage
