module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCounterexampleTargets
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerProgramsProof
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorProgramsProof
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Proof
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

private theorem positive_primitive : Primrec positive := by
  have hb : Primrec (fun p : List Nat × (Nat × Bool) => decide (0<p.2.1) && p.2.2) :=
    Primrec.and.comp (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)).decide
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Nat => xs.foldr (fun x b => decide (0<x) && b) true) :=
    Primrec.list_foldr Primrec.id (Primrec.const true) hb.to₂
  apply hf.of_eq
  intro xs
  unfold positive SourceGammaCounterexample.positive
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem compare_primitive : Primrec (fun p : Option Nat × Option Nat => compareResults p.1 p.2) := by
  have hb : Primrec (fun p : ((Option Nat × Option Nat) × Nat) × Nat => decide (p.2<p.1.2)) :=
    (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide
  have hr : Primrec (fun p : (Option Nat × Option Nat) × Nat =>
      p.1.2.casesOn (motive := fun _ => Bool) false (fun r => decide (r<p.2))) :=
    Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const false) hb.to₂
  have h := Primrec.option_casesOn (Primrec.fst (α := Option Nat) (β := Option Nat))
    (Primrec.const false) hr.to₂
  exact h.of_eq (fun p => by rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)

private theorem computable_ite {P A : Type} [Primcodable P] [Primcodable A]
    {p : P → Prop} [DecidablePred p] {f g : P → A}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => if p x then f x else g x) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private abbrev BranchInput := (Nat × List Nat) × (Nat × Nat × Nat)

private theorem branch_computable (b : Nat) : Computable (fun p : BranchInput =>
    if p.1.2.length=p.2.1 ∧ positive p.1.2=true then
      compareResults (ParametricRestrictedSourceEvaluator.gammaEvaluate b p.2.1 p.2.2.1 p.1.2)
        (ParametricRestrictedSourceEvaluator.gammaEvaluate b p.2.1 p.2.2.2 p.1.2)
    else false) := by
  have hx : Primrec (fun p : BranchInput => p.1.2) := Primrec.snd.comp Primrec.fst
  have hn : Primrec (fun p : BranchInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : BranchInput => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : BranchInput => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hg : PrimrecPred (fun p : BranchInput => p.1.2.length=p.2.1 ∧ positive p.1.2=true) :=
    (Primrec.eq.comp (Primrec.list_length.comp hx) hn).and
      (Primrec.eq.comp (positive_primitive.comp hx) (Primrec.const true))
  have heval := ParametricRestrictedSourceEvaluator.Proof.fixedGammaComputable b
  have hleft := heval.comp (hn.pair (hl.pair hx)).to_comp
  have hright := heval.comp (hn.pair (hr.pair hx)).to_comp
  exact computable_ite hg (compare_primitive.to_comp.comp (hleft.pair hright)) (Computable.const false)

/-- Each fixed gamma has a total computable raw counterexample test. -/
theorem fixedComputable : Targets.FixedComputable := by
  intro b
  have hu : Computable (fun p : Nat × List Nat =>
      (SourceMachineQueryCode.unpack p.1).casesOn (motive := fun _ => Bool) false (fun q =>
        if p.2.length=q.1 ∧ positive p.2=true then
          compareResults (ParametricRestrictedSourceEvaluator.gammaEvaluate b q.1 q.2.1 p.2)
            (ParametricRestrictedSourceEvaluator.gammaEvaluate b q.1 q.2.2 p.2)
        else false)) :=
    Computable.option_casesOn (SourceMachineQueryCode.Proof.unpack_primitive.comp Primrec.fst).to_comp
      (Computable.const false) (branch_computable b).to₂
  have hi : PrimrecPred (fun p : Nat × List Nat =>
      SourceRestrictedSyntaxChecker.restrictedCode p.1=false) :=
    Primrec.eq.comp (SourceRestrictedSyntaxChecker.Proof.uniformPrimitiveRecursive.2.2.comp Primrec.fst)
      (Primrec.const false)
  exact computable_ite hi (Computable.const true) hu

/-- Invalid syntax is rejected immediately; missing evaluations never witness failure. -/
theorem explicitFailures : Targets.ExplicitFailures := by
  constructor
  · intro b code xs h
    simp [counterexample,h]
  · constructor
    · intro x
      cases x <;> exact ⟨rfl,rfl⟩
    · intro left right
      simp [compareResults]
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Proof
