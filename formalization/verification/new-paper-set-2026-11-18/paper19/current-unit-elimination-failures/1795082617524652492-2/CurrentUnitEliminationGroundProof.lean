module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationASTProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan

private theorem inputsExt {Γ : List Ty} (ρ : Variable Γ .ground → Nat) (x y : Nat) :
    inputs (extend (extend ρ y) x) = AbsoluteObserver.extend (inputs ρ) x y := by
  funext c
  rcases c with ⟨τ,v,i⟩
  cases v with
  | here => rfl
  | there w =>
    cases w with
    | here => rfl
    | there z => cases τ <;> rfl

private theorem observeEq (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : Variable Γ .ground → Nat) (l r : Input Γ .ground) :
    InputNormalization.sourceValue p f ρ l = InputNormalization.sourceValue p f ρ r ↔
      PolicyCollision.rawScalar p f (inputs ρ) l.term =
      PolicyCollision.rawScalar p f (inputs ρ) r.term := by
  unfold InputNormalization.sourceValue
  have hl := (PolicyObservation.observationCalibration p f Γ (inputs ρ) l.term).1
  have hr := (PolicyObservation.observationCalibration p f Γ (inputs ρ) r.term).1
  constructor
  · intro h
    exact hl.symm.trans ((congrArg (fun x : Nat => x+1) h).trans hr)
  · intro h
    rw [h]

private theorem groundMatrix (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} {τ : Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) (ρ : Variable Γ .ground → Nat)
    (n x y : Nat) :
    (groundGraph p f hg a).matrix.eval p f (extend (extend (extend ρ n) y) x) = true ↔
    let ν := AbsoluteObserver.extend (inputs ρ) x y
    PolicyCollision.rawScalar p f ν (AbsoluteProbeDAG.originalInput a).term =
      PolicyCollision.rawScalar p f ν (AbsoluteProbeDAG.closedInput hg a).term ∧
    AbsoluteObserver.factor τ * (n+1) + (x+1) = AbsoluteObserver.factor τ *
      CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,a⟩) + (y+1) := by
  let ren : Renaming (.ground :: .ground :: Γ) (.ground :: .ground :: .ground :: Γ) :=
    Renaming.lift (Renaming.lift (Renaming.weaken Γ .ground))
  let σ := extend (extend ρ y) x
  let ν := extend (extend (extend ρ n) y) x
  have he : ∀ z, ν (ren z) = σ z := by
    intro z
    cases z with
    | here => rfl
    | there z =>
      cases z with
      | here => rfl
      | there z => rfl
  let l := AbsoluteProbeDAG.originalInput a
  let r := AbsoluteProbeDAG.closedInput hg a
  have hL := SourceAST.sourceValue_rename p f ren σ ν he l
  have hR := SourceAST.sourceValue_rename p f ren σ ν he r
  change ((SourceAST.Formula.conj
    (.eq (.observation (ScopedDAG.renameInput ren l)) (.observation (ScopedDAG.renameInput ren r)))
    (.eq (.add (times (AbsoluteObserver.factor τ) (raw (.there (.there .here)))) (raw .here))
      (.add (.literal (AbsoluteObserver.factor τ * CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,a⟩)))
        (raw (.there .here))))).eval p f ν = true) ↔ _
  simp only [SourceAST.Formula.eval,Bool.and_eq_true,SourceAST.Term.eval,
    decide_eq_true_eq,hL,hR,evalTimes,evalRaw]
  change ((InputNormalization.sourceValue p f σ l = InputNormalization.sourceValue p f σ r) ∧
    AbsoluteObserver.factor τ * (n+1) + (x+1) =
      AbsoluteObserver.factor τ * CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,a⟩) + (y+1)) ↔ _
  rw [observeEq]
  change (_ ∧ _) ↔ (_ ∧ _)
  have H := inputsExt ρ x y
  change inputs σ = AbsoluteObserver.extend (inputs ρ) x y at H
  rw [H]

private theorem groundFiber (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} {τ : Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) (ρ : Variable Γ .ground → Nat) (n : Nat) :
    (groundGraph p f hg a).holds p f ρ n ↔ CurrentAbsolute.Formula p f hg a (inputs ρ) (n+1) := by
  constructor
  · rintro ⟨ω,hρ,hn,hM⟩
    let x := ω .here
    let y := ω (.there .here)
    have hω : ω = extend (extend (extend ρ n) y) x := by
      funext z
      cases z with
      | here => rfl
      | there z =>
        cases z with
        | here => rfl
        | there z =>
          cases z with
          | here => exact hn
          | there z => exact hρ z
    rw [hω] at hM
    obtain ⟨he,hlin⟩ := (groundMatrix p f hg a ρ n x y).1 hM
    exact ⟨x,y,he,hlin⟩
  · rintro ⟨x,y,he,hlin⟩
    exact ⟨extend (extend (extend ρ n) y) x,fun _ => rfl,rfl,
      (groundMatrix p f hg a ρ n x y).2 ⟨he,hlin⟩⟩

theorem exactGround : CurrentUnitEliminationTargets.ExactGround := by
  intro p f h Γ τ hg a ρ r
  have exactA := CurrentAbsolute.StatementChecks.fixed_absolute.2.2.2 p f h Γ τ hg a (inputs ρ)
  constructor
  · rintro ⟨n,rfl,hn⟩
    exact (exactA (n+1)).1 ((groundFiber p f hg a ρ n).1 hn)
  · intro hr
    obtain ⟨n,hn,hs⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) a.term
    have e := CurrentAbsolute.scalar_unique p f (inputs ρ) a.term r n hr hs
    have hrpos : 0 < r := e.symm ▸ hn
    have add : r-1+1 = r := by omega
    refine ⟨r-1,add,(groundFiber p f hg a ρ (r-1)).2 ?_⟩
    rw [add]
    exact (exactA r).2 hr

theorem groundConjunctive (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} {τ : Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) : Conjunctive (groundGraph p f hg a).matrix :=
  ⟨⟨trivial,trivial⟩,
    ⟨⟨timesLinear _ _ (rawLinear _),rawLinear _⟩,⟨trivial,rawLinear _⟩⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
