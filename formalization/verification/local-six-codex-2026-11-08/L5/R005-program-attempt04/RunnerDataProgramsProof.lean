module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCodeProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmBaseProgramsProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
open PolynomialGraphCompletion Algorithm AlgorithmPrograms

theorem branchGuard_primitive : Primrec (fun b : EncodedBranch => b.2.1) := Primrec.fst.comp Primrec.snd
theorem branchAction_primitive : Primrec (fun b : EncodedBranch => b.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem branchTag_primitive : Primrec (fun b : EncodedBranch => b.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem branchRow_primitive : Primrec (fun b : EncodedBranch => b.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem branchWork_primitive : Primrec₂ branchWork :=
  Primrec.ite (Primrec.eq.comp (branchAction_primitive.comp Primrec.snd) (Primrec.const 1))
    (Primrec.option_some.comp ((branchRow_primitive.comp Primrec.snd).pair
      (conjunction_encode_primitive.comp (Primrec.snd.comp Primrec.fst)
        (branchGuard_primitive.comp Primrec.snd)))) (Primrec.const none)

theorem branchFinished_primitive : Primrec₂ branchFinished :=
  Primrec.ite (Primrec.eq.comp (branchAction_primitive.comp Primrec.snd) (Primrec.const 0))
    (Primrec.option_some.comp ((conjunction_encode_primitive.comp (Primrec.snd.comp Primrec.fst)
      (branchGuard_primitive.comp Primrec.snd)).pair
      (Primrec.list_cons.comp ((branchTag_primitive.comp Primrec.snd).pair
        (branchRow_primitive.comp Primrec.snd)) (Primrec.const [])))) (Primrec.const none)

theorem initial_primitive : Primrec initial :=
  rowTail_primitive.pair ((Primrec.list_cons.comp
    (Primrec.id.pair (Primrec.const 0)) (Primrec.const [])).pair (Primrec.const []))

theorem admitted_primitive : Primrec₂ Runner.admitted := by
  let A := Nat × Row
  have hword : Primrec (fun p : A × (Item × Bool) =>
      FullWordGuardCompletion.admittedWord p.1.1 p.2.1.2.2) :=
    FullWordGuardCompletion.RunnerProgramsProof.admittedWord_primitive.comp
      ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  have hs := Primrec.and.comp hword (Primrec.snd.comp Primrec.snd)
  have hall : Primrec (fun p : A => p.2.2.all
      (fun a => FullWordGuardCompletion.admittedWord p.1 a.2.2)) := by
    apply (Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const true) hs.to₂).of_eq
    intro p
    induction p.2.2 with
    | nil => rfl
    | cons a xs ih =>
        simpa only [List.all_cons] using
          (congrArg (fun b => FullWordGuardCompletion.admittedWord p.1 a.2.2 && b) ih)
  have hdegree : Primrec (fun p : A => decide (3 ≤ p.1)) := by
    apply (Primrec.ite (Primrec.nat_le.comp (Primrec.const 3) Primrec.fst)
      (Primrec.const true) (Primrec.const false)).of_eq
    intro p
    by_cases h : 3 ≤ p.1 <;> simp [h]
  exact Primrec.and.comp hdegree hall

theorem collectOptions_primitive {β : Type} [Primcodable β] :
    Primrec (fun xs : List (Option β) => xs.filterMap id) :=
  Primrec.listFilterMap Primrec.id Primrec.snd

theorem computable_filterMap {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → β → Option σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).filterMap (g a)) := by
  apply (collectOptions_primitive.to_comp.comp (computable_map default hf hg)).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b xs ih => cases h : g a b <;> simp [h,ih]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
