module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationASTProof
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationWireProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open CurrentOneUnit ExistentialPlan

theorem rawSucc (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (q : OpenGraph Γ) (ρ : Variable Γ .ground → Nat) (n : Nat) :
    HoldsRaw p f q ρ (n+1) ↔ q.holds p f ρ n := by
  constructor
  · rintro ⟨k,h,hh⟩
    exact (Nat.add_right_cancel h : k=n) ▸ hh
  · exact fun h => ⟨n,rfl,h⟩

theorem holdsFilled (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (q : OpenGraph Γ) (ρ : Variable Γ .ground → Nat) (n : Nat) :
    q.holds p f ρ n ↔ ∃ v : Variable (WireCtx q.width (.ground :: Γ)) .ground → Nat,
      q.matrix.eval p f (fillPrefix q.width v (extend ρ n)) = true := by
  constructor
  · rintro ⟨ω,hρ,hn,hM⟩
    have H : ∀ x, ω (shift q.width x) = extend ρ n x := by
      intro x
      cases x with
      | here => exact hn
      | there x => exact hρ x
    exact ⟨ω,by rwa [prefixReduction q.width ω (extend ρ n) H]⟩
  · rintro ⟨v,hv⟩
    refine ⟨fillPrefix q.width v (extend ρ n),?_,?_,hv⟩
    · intro x
      exact fillShift q.width v (extend ρ n) (.there x)
    · exact fillShift q.width v (extend ρ n) .here

theorem routeHolds (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ Δ : List Ty}
    (q : OpenGraph Γ) (r : Renaming (WireCtx q.width Γ) Δ) (z : Variable Δ .ground)
    (ω : Variable Δ .ground → Nat) (ρ : Variable Γ .ground → Nat)
    (h : ∀ x, ω (r (shift q.width x)) = ρ x)
    (hm : q.matrix.eval p f (fun x => ω (reroute q.width r z x)) = true) :
    q.holds p f ρ (ω z) := by
  refine ⟨fun x => ω (reroute q.width r z x),?_,?_,hm⟩
  · intro x
    have he := congrFun (reroutePull q.width r z ω) (shift q.width (.there x))
    rw [he,fillShift]
    exact h x
  · have he := congrFun (reroutePull q.width r z ω) (shift q.width (.here : Variable (.ground :: Γ) .ground))
    rw [he,fillShift] <;> rfl

theorem routeFill {Γ Δ Θ : List Ty} (n : Nat) (r : Renaming (WireCtx n Γ) Δ)
    (z : Variable Δ .ground) (ω : Variable Δ .ground → Nat)
    (ρ : Variable Γ .ground → Nat) (v : Variable (WireCtx n Θ) .ground → Nat) (l : Nat)
    (hv : (fun x => ω (r x)) = fillPrefix n v ρ) (hz : ω z = l) :
    (fun x => ω (reroute n r z x)) = fillPrefix n v (extend ρ l) := by
  have hρ : (fun x => ω (r (shift n x))) = ρ := by
    funext x
    exact (congrFun hv (shift n x)).trans (fillShift n v ρ x)
  rw [reroutePull,hv,hρ,hz,fillReset]

private def freeBase (Γ : List Ty) (n : Nat) :
    Renaming (WireCtx n Γ) (.ground :: WireCtx n (.ground :: Γ)) :=
  fun x => .there (under (Renaming.weaken Γ .ground) n x)

theorem freeMatrix (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (row : LinearCode) (q : OpenGraph Γ)
    (ω : Variable (.ground :: WireCtx q.width (.ground :: Γ)) .ground → Nat) :
    (freeGraph row q).matrix.eval p f ω = true ↔
      q.matrix.eval p f (fun x => ω (reroute q.width (freeBase Γ q.width) .here x)) = true ∧
      holds row (ω .here+1) 0 (ω (.there (shift q.width .here))+1) := by
  change ((SourceAST.Formula.conj
    (renameFormula (reroute q.width (freeBase Γ q.width) .here) q.matrix)
    (rowFormula row (raw .here) (.literal 0) (raw (.there (shift q.width .here))))).eval p f ω = true) ↔ _
  simp only [SourceAST.Formula.eval,Bool.and_eq_true,formulaEvalRename,evalRow,evalRaw,SourceAST.Term.eval]

theorem exactFreeNat (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : Variable Γ .ground → Nat) (row : LinearCode) (q : OpenGraph Γ) (n : Nat) :
    (freeGraph row q).holds p f ρ n ↔
      ∃ l : Nat, q.holds p f ρ l ∧ holds row (l+1) 0 (n+1) := by
  constructor
  · rintro ⟨ω,hρ,hn,hM⟩
    obtain ⟨hQ,hR⟩ := (freeMatrix p f row q ω).1 hM
    refine ⟨ω .here,routeHolds p f q (freeBase Γ q.width) .here ω ρ ?_ hQ,?_⟩
    · intro x
      change ω (.there (under (Renaming.weaken Γ .ground) q.width (shift q.width x))) = _
      rw [pullShiftUnder]
      exact hρ x
    · change ω (.there (shift q.width .here)) = n at hn
      rwa [hn] at hR
  · rintro ⟨l,hQ,hR⟩
    obtain ⟨v,hv⟩ := (holdsFilled p f q ρ l).1 hQ
    let ω : Variable (.ground :: WireCtx q.width (.ground :: Γ)) .ground → Nat :=
      extend (fillPrefix q.width v (extend ρ n)) l
    have hbase : (fun x => ω (freeBase Γ q.width x)) = fillPrefix q.width v ρ := by
      funext x
      change fillPrefix q.width v (extend ρ n) (under (Renaming.weaken Γ .ground) q.width x) = _
      exact fillUnder q.width (Renaming.weaken Γ .ground) v (extend ρ n) x
    have e := routeFill q.width (freeBase Γ q.width) .here ω ρ v l hbase rfl
    refine ⟨ω,?_,?_,(freeMatrix p f row q ω).2 ⟨?_,?_⟩⟩
    · intro x
      exact fillShift q.width v (extend ρ n) (.there x)
    · exact fillShift q.width v (extend ρ n) .here
    · rwa [e]
    · have h := fillShift q.width v (extend ρ n) .here
      change holds row (l+1) 0 (fillPrefix q.width v (extend ρ n) (shift q.width .here)+1)
      rwa [h]

theorem freeConjunctive {Γ : List Ty} (row : LinearCode) (q : OpenGraph Γ)
    (h : Conjunctive q.matrix) : Conjunctive (freeGraph row q).matrix :=
  ⟨formulaRetainsGrammar _ _ h,rowConjunctive row _ _ _ (rawLinear _) trivial (rawLinear _)⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
