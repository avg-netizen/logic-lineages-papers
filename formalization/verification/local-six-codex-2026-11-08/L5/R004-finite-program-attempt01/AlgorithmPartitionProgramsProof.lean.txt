module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmRowProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmTailProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsMaskProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion Algorithm
open LayeredComparison.SnyatkovCompletion

theorem labelled_primitive : Primrec₂ labelled :=
  (LayeredComparison.CommonHeadCode.Program.zipWith_primitive Prod.mk Primrec₂.pair).comp
    (active_primitive.comp Primrec.fst) Primrec.snd

theorem leaderClass_primitive : Primrec₂ leaderClass := by
  have hp : Primrec₂ (fun label : Nat => fun a : Labelled => a.2 == label) :=
    Primrec.beq.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hf := (InactivePhiProgramsProof.filterWith_primitive hp).comp Primrec.snd Primrec.fst
  exact Primrec.list_map hf (Primrec.fst.comp Primrec.snd).to₂

theorem classes_primitive : Primrec₂ classes := by
  have hz : Primrec (fun p : Row × List Nat => labelled p.1 p.2) :=
    labelled_primitive.comp Primrec.fst Primrec.snd
  have hc := Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp
    (active_primitive.comp Primrec.fst)))
    (leaderClass_primitive.comp (hz.comp Primrec.fst) Primrec.snd).to₂
  have hnonempty : PrimrecPred (fun xs : List Item => xs ≠ []) :=
    (Primrec.eq.comp Primrec.id (Primrec.const ([] : List Item))).not
  apply ((Primrec.listFilter hnonempty).comp hc).of_eq
  intro p
  apply List.filter_congr
  intro xs
  simp

theorem outside_primitive : Primrec (fun p : Row × List Nat × Nat => outside p.1 p.2.1 p.2.2) := by
  let A := Row × List Nat × Nat
  have hz : Primrec (fun p : A => labelled p.1 p.2.1) :=
    labelled_primitive.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hp : Primrec₂ (fun label : Nat => fun a : Labelled => a.2 != label) :=
    Primrec.not.comp (Primrec.beq.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have hf := (InactivePhiProgramsProof.filterWith_primitive hp).comp
    (Primrec.snd.comp Primrec.snd) hz
  exact Primrec.list_append.comp (linearPart_primitive.comp Primrec.fst)
    (Primrec.list_map hf (Primrec.fst.comp Primrec.snd).to₂)

theorem rewrite_primitive :
    Primrec (fun p : Nat × Row × List Nat × Nat => rewrite p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Row × List Nat × Nat
  have hr : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hz := labelled_primitive.comp hr hl
  have hc := leaderClass_primitive.comp hz hn
  have hrep := classReplacement_primitive.comp Primrec.fst hc
  have hout := outside_primitive.comp (hr.pair (hl.pair hn))
  exact (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp
    (Primrec.fst.comp hr) (Primrec.fst.comp hrep)).pair
    (Primrec.list_append.comp hout (Primrec.snd.comp hrep))

theorem zeroClass_primitive : Primrec₂ zeroClass := by
  let A := Row × List Nat
  have hz : Primrec (fun p : A => labelled p.1 p.2) := labelled_primitive.comp Primrec.fst Primrec.snd
  have hclass : Primrec (fun p : A × (Nat × Option Nat) =>
      leaderClass (labelled p.1.1 p.1.2) p.2.1) :=
    leaderClass_primitive.comp (hz.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hpred := Primrec.and.comp
    (Primrec.not.comp (Primrec.beq.comp hclass (Primrec.const ([] : List Item))))
    (Primrec.beq.comp (leading_primitive.comp hclass) (Primrec.const (0 : Int)))
  have hs : Primrec₂ (fun p : A => fun state : Nat × Option Nat =>
      bif !(leaderClass (labelled p.1 p.2) state.1).isEmpty &&
          leading (leaderClass (labelled p.1 p.2) state.1) == 0
        then some state.1 else state.2) := by
    apply (Primrec.cond hpred
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).of_eq
    intro p
    cases h : leaderClass (labelled p.1.1 p.1.2) p.2.1 <;> simp [h]
  have hf := Primrec.list_foldr
    (Primrec.list_range.comp (Primrec.list_length.comp (active_primitive.comp Primrec.fst)))
    (Primrec.const (none : Option Nat)) hs
  apply hf.of_eq
  intro p
  unfold zeroClass
  induction List.range (active p.1).length with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.foldr_cons,List.find?_cons,ih]
      cases h : !(leaderClass (labelled p.1 p.2) label).isEmpty &&
          leading (leaderClass (labelled p.1 p.2) label) == 0 <;> simp [h]

theorem assignments_primitive : Primrec₂ assignments := by
  let A := Nat × List (List Nat)
  have hi : Primrec (fun p : A × Nat => p.1.2.map (fun labels => p.2::labels)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hext : Primrec (fun p : A => (List.range p.1).flatMap
      (fun label => p.2.map (fun labels => label::labels))) :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst) hi.to₂
  have hs : Primrec₂ (fun p : Nat × Nat => fun state : Nat × List (List Nat) =>
      (List.range p.1).flatMap (fun label => state.2.map (fun labels => label::labels))) :=
    hext.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))
  apply (Primrec.nat_rec' Primrec.snd (Primrec.const ([[]] : List (List Nat))) hs).of_eq
  intro p
  rcases p with ⟨bound,n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [assignments] using congrArg
        (fun lists => (List.range bound).flatMap (fun label => lists.map (fun labels => label::labels))) ih

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
