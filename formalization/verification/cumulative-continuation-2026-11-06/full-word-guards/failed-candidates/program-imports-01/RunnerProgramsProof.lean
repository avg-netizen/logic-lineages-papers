module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerTargets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProgramsProof
private import LogicLineages.OrdinalComparison.CanonicalGuardSelector.ProgramsProof
private import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProgramsProof
open PolynomialGraphCompletion CanonicalGuardSelector GuardChildMeasureCompletion
open ComparisonProgramsProof DispatchProgramsProof

private theorem listAll_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Bool} (hp : Primrec₂ p) :
    Primrec₂ (fun (a : α) (xs : List β) => xs.all (p a)) := by
  let A := α × List β
  have hs : Primrec (fun q : A × (β × Bool) => p q.1.1 q.2.1 && q.2.2) :=
    Primrec.and.comp
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun q : A => q.2.foldr (fun b s => p q.1 b && s) true) :=
    Primrec.list_foldr Primrec.snd (Primrec.const true) hs.to₂
  apply hf.to₂.of_eq
  intro a xs
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.foldr_cons, List.all_cons, ih]

theorem admittedLetter_primitive :
    Primrec (fun p : Nat × Letter => admittedLetter p.1 p.2) := by
  have hD : Primrec (fun p : Nat × Letter => p.1) := Primrec.fst
  have htag : Primrec (fun p : Nat × Letter => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hdegree : Primrec (fun p : Nat × Letter => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.nat_le.comp htag (Primrec.const 2)) (Primrec.const true)
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.or.comp (Primrec.beq.comp htag (Primrec.const 3))
          (Primrec.beq.comp htag (Primrec.const 4)))
        (Primrec.nat_le.comp (Primrec.const 3) hdegree).decide)
      (Primrec.nat_le.comp hdegree hD).decide)

theorem admittedWord_primitive :
    Primrec (fun p : Nat × Word => admittedWord p.1 p.2) :=
  listAll_primitive admittedLetter_primitive

theorem admitted_primitive :
    Primrec (fun p : Nat × WordPair => admitted p.1 p.2) :=
  Primrec.and.comp
    (admittedWord_primitive.comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
    (admittedWord_primitive.comp
      (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))

theorem initial_primitive : Primrec initial :=
  Primrec.id.pair ((Primrec.const 0).pair (Primrec.const 1))

theorem step_primitive : Primrec step := by
  have ho : Primrec (fun s : State => selectWords s.1.1 s.1.2) :=
    CanonicalGuardSelector.Proof.selectWords_primitive.comp Primrec.fst
  have hp : Primrec (fun p : State × Choice => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hchild : Primrec (fun p : State × Choice => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htail : Primrec (fun p : State × Choice => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have htie : Primrec (fun p : State × Choice => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hb := hchild.pair
    ((Primrec.nat_max.comp htail (dispatchTail_primitive.comp hp)).pair
      (liftTie_primitive.comp htie (dispatchTie_primitive.comp hp)))
  apply (Primrec.option_casesOn ho Primrec.id hb.to₂).of_eq
  intro s
  unfold step
  cases selectWords s.1.1 s.1.2 <;> rfl

theorem run_primitive : Primrec (fun p : WordPair × Nat => run p.1 p.2) :=
  Primrec.nat_iterate Primrec.snd (initial_primitive.comp Primrec.fst)
    (step_primitive.comp Primrec.snd).to₂

theorem paidTail_primitive : Primrec paidTail :=
  Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.nat_max.comp
      (WordGuardCompletion.Proof.wordTail_primitive.comp (Primrec.fst.comp Primrec.fst))
      (WordGuardCompletion.Proof.wordTail_primitive.comp (Primrec.snd.comp Primrec.fst)))

theorem stopped_primitive :
    Primrec (fun p : Nat × WordPair × Nat => stopped p.1 p.2.1 p.2.2) := by
  let P := Nat × WordPair × Nat
  have hr : Primrec (fun p : P => run p.2.1 p.2.2) :=
    run_primitive.comp Primrec.snd
  have hq := CanonicalGuardSelector.Proof.selectWords_primitive.comp (Primrec.fst.comp hr)
  have hn : Primrec (fun p : P =>
      (selectWords (run p.2.1 p.2.2).1.1 (run p.2.1 p.2.2).1.2).isNone) := by
    apply (Primrec.not.comp (Primrec.option_isSome.comp hq)).of_eq
    intro p
    cases selectWords (run p.2.1 p.2.2).1.1 (run p.2.1 p.2.2).1.2 <;> rfl
  exact Primrec.or.comp
    (Primrec.not.comp (admitted_primitive.comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))) hn

theorem runnerPrograms : RunnerTargets.RunnerPrograms :=
  ⟨admitted_primitive, initial_primitive, step_primitive, run_primitive,
    paidTail_primitive, stopped_primitive⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProgramsProof
