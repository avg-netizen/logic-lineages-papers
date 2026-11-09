module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm Runner
open LogicLineages.ModelsAlgebra.Forests

def GuardSyntax (D maximum : Nat) (names : List Nat) (p : Formula) : Prop :=
  Formula.allowed D p ∧ linear maximum p = true ∧ FormulaNamesFrom names p

def WorkSyntax (D maximum : Nat) (names : List Nat) (w : Work) : Prop :=
  GuardSyntax D maximum names w.guard ∧ RowAllowed D w.row ∧ NamesFrom names w.row

def CaseSyntax (D maximum : Nat) (names : List Nat) (c : RowCase) : Prop :=
  GuardSyntax D maximum names c.guard ∧ c.outcomes.length = 1 ∧
  ∀ o ∈ c.outcomes, RowAllowed D o.row ∧ NamesFrom names o.row ∧
    (o.tag = 0 ∨ o.tag = 2 ∨ (o.tag = 3 ∧ LinearRow maximum o.row))

noncomputable def WorkMeaning (source : Row) (w : Work) (ν : Nat → Nat) : Prop :=
  Formula.meaningful w.guard ν ∧ RowDomain w.row ν ∧
    (Formula.eval ν w.guard → RowValue w.row ν = RowValue source ν)

noncomputable def CaseMeaning (maximum : Nat) (source : Row) (c : RowCase) (ν : Nat → Nat) : Prop :=
  Formula.meaningful c.guard ν ∧ (∀ o ∈ c.outcomes, RowDomain o.row ν) ∧
    (Formula.eval ν c.guard → List.Forall₂ (fun r o => OutcomeCorrect maximum r o ν) [source] c.outcomes)

/-- Literal pending/finished source invariant. There is no consistency test
or invariant field supplied to the actual work-stack program. -/
noncomputable def Invariant (D maximum : Nat) (source : Row) (s : State) : Prop :=
  (∀ w ∈ s.work, WorkSyntax D maximum (rowVariables source) w) ∧
  (∀ c ∈ s.finished, CaseSyntax D maximum (rowVariables source) c) ∧
  ∀ ν, Region s.paid maximum (rowVariables source) ν →
    RowDomain source ν ∧ (∀ w ∈ s.work, WorkMeaning source w ν) ∧
    (∀ c ∈ s.finished, CaseMeaning maximum source c ν) ∧
    ((∃ w ∈ s.work, Formula.eval ν w.guard) ∨ ∃ c ∈ s.finished, Formula.eval ν c.guard)

theorem conj_tokens (p q : Formula) : Formula.tokens (.conj p q) = p.tokens++q.tokens := by
  simp [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

theorem conj_guard_syntax (D maximum : Nat) (names : List Nat) (p q : Formula)
    (hp : GuardSyntax D maximum names p) (hq : GuardSyntax D maximum names q) :
    GuardSyntax D maximum names (.conj p q) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    rw [conj_tokens] at ht
    exact (List.mem_append.mp ht).elim (hp.1 t) (hq.1 t)
  · simp only [linear,conj_tokens,List.all_append,Bool.and_eq_true]
    exact ⟨hp.2.1,hq.2.1⟩
  · intro i hi
    have hm : i ∈ Formula.variables p ∨ i ∈ Formula.variables q := by
      simpa [Formula.variables,conj_tokens,List.map_append] using hi
    exact hm.elim (hp.2.2 i) (hq.2.2 i)

theorem conj_guard_meaningful (p q : Formula) (ν : Nat → Nat)
    (hp : Formula.meaningful p ν) (hq : Formula.meaningful q ν) :
    Formula.meaningful (.conj p q) ν := by
  intro t ht
  rw [conj_tokens] at ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

theorem region_mono (lo hi maximum : Nat) (names : List Nat) (ν : Nat → Nat)
    (hle : lo ≤ hi) (hr : Region hi maximum names ν) : Region lo maximum names ν := by
  intro i hi
  exact ⟨hle.trans (hr i hi).1,(hr i hi).2⟩

theorem outcomeCorrect_transfer (maximum : Nat) (source middle : Row) (o : Outcome) (ν : Nat → Nat)
    (he : RowValue middle ν = RowValue source ν) (ho : OutcomeCorrect maximum middle o ν) :
    OutcomeCorrect maximum source o ν := by
  rcases ho with ⟨htag,hneg⟩ | ⟨htag,hpos⟩ | ⟨htag,hlinear,hvalue⟩
  · exact Or.inl ⟨htag,by rwa [he] at hneg⟩
  · exact Or.inr (Or.inl ⟨htag,by rwa [he] at hpos⟩)
  · exact Or.inr (Or.inr ⟨htag,hlinear,hvalue.trans he⟩)

theorem initial_invariant (D maximum : Nat) (source : Row) (hD : RowAllowed D source) :
    Invariant D maximum source (initial source) := by
  refine ⟨?_,by simp [initial],?_⟩
  · intro w hw
    have he : w = ⟨source,.top⟩ := by simpa [initial] using hw
    subst w
    refine ⟨?_,hD,fun i hi => hi⟩
    simp [GuardSyntax,Formula.allowed,linear,FormulaNamesFrom,Formula.variables,Formula.tokens,
      CotreePresburgerUnit.Boolean.atoms]
  · intro ν hregion
    have hd : RowDomain source ν := AlgorithmProof.rowTail_domain D source ν hD
      (fun i hi => (hregion i hi).1)
    refine ⟨hd,?_,by simp [initial],Or.inl ⟨⟨source,.top⟩,by simp [initial],True.intro⟩⟩
    intro w hw
    have he : w = ⟨source,.top⟩ := by simpa [initial] using hw
    subst w
    refine ⟨?_,hd,fun _ => rfl⟩
    simp [Formula.meaningful,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]

theorem finish_invariant_correct (D maximum : Nat) (source : Row) (s : State)
    (hi : Invariant D maximum source s) (hempty : s.work = []) :
    PackageCorrect D maximum [source] (finish s) := by
  constructor
  · intro c hc
    rcases hi.2.1 c hc with ⟨hg,hcount,hout⟩
    rcases hg with ⟨ha,hl,hn⟩
    exact ⟨ha,hl,by simpa [OriginalNames] using hn,by simpa using hcount,
      fun o ho => ⟨(hout o ho).1,by simpa [OriginalNames] using (hout o ho).2.1,(hout o ho).2.2⟩⟩
  · intro ν hregion
    have hr : Region s.paid maximum (rowVariables source) ν := by
      simpa [finish,OriginalNames] using hregion
    rcases hi.2.2 ν hr with ⟨hdom,hwork,hcases,hcover⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro r hr
      have he : r = source := by simpa using hr
      subst r
      exact hdom
    · intro c hc
      exact ⟨(hcases c hc).1,(hcases c hc).2.1⟩
    · rcases hcover with ⟨w,hw,htrue⟩ | hcover
      · simp [hempty] at hw
      · exact hcover
    · intro c hc htrue
      exact (hcases c hc).2.2 htrue

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
