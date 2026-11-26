module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationRenderProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan

private def Ready (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (a : OriginalTerm Γ τ) (q : Tree Γ) : Prop :=
  depth q ≤ functionalCount Γ ∧ EveryScalarUnique p f q ∧
  ∀ (ρ : Variable Γ .ground → Nat) (r : Nat),
    q.holds p f ρ r ↔ CurrentAbsolute.Scalar p f (inputs ρ) a r

private theorem readyUnique (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (a : OriginalTerm Γ τ) (q : Tree Γ) (h : Ready p f a q)
    (ρ : Variable Γ .ground → Nat) (r s : Nat)
    (hr : q.holds p f ρ r) (hs : q.holds p f ρ s) : r=s :=
  CurrentAbsolute.scalar_unique p f (inputs ρ) a r s ((h.2.2 ρ r).1 hr) ((h.2.2 ρ s).1 hs)

private theorem sourcePos (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (a : OriginalTerm Γ τ) (ρ : Variable Γ .ground → Nat) (r : Nat)
    (h : CurrentAbsolute.Scalar p f (inputs ρ) a r) : 0 < r := by
  obtain ⟨n,hn,he⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) a
  exact (CurrentAbsolute.scalar_unique p f (inputs ρ) a r n h he).symm ▸ hn

private theorem treePos (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (q : Tree Γ) (ρ : Variable Γ .ground → Nat) (r : Nat) (h : q.holds p f ρ r) : 0 < r := by
  obtain ⟨n,hn,_⟩ := h
  omega

private theorem zeroFiber (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (a : OriginalTerm Γ τ) (q : Tree Γ) (ρ : Variable Γ .ground → Nat) :
    q.holds p f ρ 0 ↔ CurrentAbsolute.Scalar p f (inputs ρ) a 0 :=
  ⟨fun h => False.elim ((Nat.lt_irrefl 0) (treePos p f q ρ 0 h)),
    fun h => False.elim ((Nat.lt_irrefl 0) (sourcePos p f a ρ 0 h))⟩

private theorem stepComplete (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) (n : Nat)
    (ih : ∀ (Γ : List Ty) (τ : Ty) (a : OriginalTerm Γ τ), Γ.length < n →
      ∃ q : Tree Γ, build p n a = some q ∧ Ready p f a q)
    {Γ τ} (s : UnitElimination.Selection Γ) (a : OriginalTerm Γ τ) (hΓ : Γ.length < n+1) :
    ∃ q : Tree Γ, step p (fun {_ _} t => build p n t) s a = some q ∧ Ready p f a q := by
  cases s with
  | ground hg =>
    let d := CurrentTreeInputCoverage.input a
    have he : d.term = a := (CurrentTreeInputCoverage.StatementChecks.actual_tree_codes _ τ a).1
    refine ⟨.leaf hg d,rfl,Nat.zero_le _,trivial,?_⟩
    intro ρ r
    have exactA := exactGround p f hf _ τ hg d ρ r
    rw [he] at exactA
    exact (treeHoldsGround p f hg d ρ r).trans exactA
  | found left right σ hs =>
    let b : OriginalTerm (σ :: (left ++ right)) τ := a.rename (SelectedBinder.moveToHead left right σ)
    obtain ⟨d,hd,_,_,_,he⟩ := CurrentOneUnit.StatementChecks.exact_selected_graph
      p f left right σ τ a hs
    change CurrentOneUnit.typedCoefficients p b = some d at hd
    have hcut : (left ++ right).length < n := by
      simp only [List.length_append,List.length_cons] at hΓ ⊢
      omega
    obtain ⟨q,hq,hR⟩ := ih (left ++ right) (.arrow σ τ) (OneUnit.first b) hcut
    let row := CurrentOneUnit.equation τ.level d
    cases hfree : d.2.2 with
    | true =>
      let z := Tree.free left right σ hs row q
      refine ⟨z,?_,?_,?_,?_⟩
      · simp only [step,Option.bind_eq_bind,Option.pure_def,hd,Option.bind_some,hq,hfree,↓reduceIte,z,row,b]
      · change depth q + 1 ≤ functionalCount (left ++ σ :: right)
        rw [functionsRemovedCount left right σ hs]
        exact Nat.add_le_add_right hR.1 1
      · exact ⟨readyUnique p f _ q hR,hR.2.1⟩
      · intro ρ r
        cases r with
        | zero => exact zeroFiber p f a z ρ
        | succ r =>
          have H := treeHoldsFree p f left right σ hs row q ρ r
          refine H.trans (Iff.trans ?_ (he ρ (r+1)))
          change (∃ l : Nat, q.holds p f (UnitObservation.remainingInputs left right σ ρ) l ∧
            CurrentOneUnit.holds row l 0 (r+1)) ↔
              CurrentOneUnit.Formula p f (UnitObservation.remainingInputs left right σ ρ) b d (r+1)
          simp only [CurrentOneUnit.Formula,hfree,↓reduceIte,hR.2.2,row]
    | false =>
      obtain ⟨s,hs',hS⟩ := ih (left ++ right) (.arrow σ (.arrow .ground τ)) (OneUnit.second b) hcut
      let z := Tree.active left right σ hs row q s
      refine ⟨z,?_,?_,?_,?_⟩
      · simp only [step,Option.bind_eq_bind,Option.pure_def,hd,Option.bind_some,hq,hs',
          hfree,Bool.false_eq_true,↓reduceIte,z,row,b]
      · change max (depth q) (depth s) + 1 ≤ functionalCount (left ++ σ :: right)
        rw [functionsRemovedCount left right σ hs]
        exact Nat.add_le_add_right (max_le hR.1 hS.1) 1
      · exact ⟨readyUnique p f _ q hR,readyUnique p f _ s hS,hR.2.1,hS.2.1⟩
      · intro ρ r
        cases r with
        | zero => exact zeroFiber p f a z ρ
        | succ r =>
          have H := treeHoldsActive p f left right σ hs row q s ρ r
          refine H.trans (Iff.trans ?_ (he ρ (r+1)))
          change (∃ l l' : Nat, q.holds p f (UnitObservation.remainingInputs left right σ ρ) l ∧
            s.holds p f (UnitObservation.remainingInputs left right σ ρ) l' ∧
            CurrentOneUnit.holds row l l' (r+1)) ↔
              CurrentOneUnit.Formula p f (UnitObservation.remainingInputs left right σ ρ) b d (r+1)
          simp only [CurrentOneUnit.Formula,hfree,Bool.false_eq_true,↓reduceIte,hR.2.2,hS.2.2,row]

private theorem buildComplete (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) (n : Nat) :
    ∀ (Γ : List Ty) (τ : Ty) (a : OriginalTerm Γ τ), Γ.length < n →
      ∃ q : Tree Γ, build p n a = some q ∧ Ready p f a q := by
  induction n with
  | zero => intro Γ τ a ha; omega
  | succ n ih =>
    intro Γ τ a hΓ
    exact stepComplete p f hf n ih (UnitElimination.select Γ) a hΓ

theorem exactSourceGraph : CurrentUnitEliminationTargets.ExactSourceGraph := by
  intro p f hf Γ τ a
  obtain ⟨q,hq,H⟩ := buildComplete p f hf (Γ.length+1) Γ τ a (Nat.lt_succ_self _)
  refine ⟨q,hq,H.1,renderConjunctive p f q,H.2.1,?_⟩
  intro ρ
  obtain ⟨r,hr,hs⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) a
  exact ⟨H.2.2 ρ,⟨r,hr,(H.2.2 ρ r).2 hs⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
