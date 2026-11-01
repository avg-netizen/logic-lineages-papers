module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerSyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

attribute [local irreducible] Nat.sqrt Nat.unpair encodedSingleCoreRowSign encodedSingleCoreBoxSign
  encodedSingleCorePresburger encodedSingleCoreUniversal encodedSingleCoreSupport singleCoreBoxWords

private theorem quote_primitive (opcode : Nat) : Primrec₂ (fun left right : List OneInputBooleanInstruction =>
    left++right++[(opcode,0,0)]) :=
  Primrec.list_append.comp (Primrec.list_append.comp Primrec.fst Primrec.snd) (Primrec.const [(opcode,0,0)])

theorem constant_primitive : Primrec singleCorePresburgerConstantCode := Primrec.dom_bool _

theorem tail_code_primitive : Primrec₂ singleCorePresburgerTailCode := by
  have hi : Primrec (fun p : (List Nat × Nat) × (Nat × List OneInputBooleanInstruction) => [(3,p.2.1,p.1.2)]) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst))) (Primrec.const [])
  have hs : Primrec₂ (fun p : List Nat × Nat => fun state : Nat × List OneInputBooleanInstruction =>
      [(3,state.1,p.2)]++state.2++[(7,0,0)]) :=
    (quote_primitive 7).comp hi (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst (Primrec.const (singleCorePresburgerConstantCode false)) hs

theorem point_code_primitive : Primrec₂ singleCorePresburgerPointCode := by
  have hsupp : Primrec (fun p : (List Nat × List Nat) × (Nat × List OneInputBooleanInstruction) =>
      p.1.1.getD p.2.1 0) := (Primrec.list_getD 0).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hword : Primrec (fun p : (List Nat × List Nat) × (Nat × List OneInputBooleanInstruction) =>
      p.1.2.getD p.2.1 1) := (Primrec.list_getD 1).comp
        (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hi := Primrec.list_cons.comp ((Primrec.const 2).pair (hsupp.pair hword)) (Primrec.const [])
  have hs : Primrec₂ (fun p : List Nat × List Nat => fun state : Nat × List OneInputBooleanInstruction =>
      [(2,p.1.getD state.1 0,p.2.getD state.1 1)]++state.2++[(6,0,0)]) :=
    (quote_primitive 6).comp hi (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    (Primrec.const (singleCorePresburgerConstantCode true)) hs

private theorem computable_if {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp hf hg

abbrev CompilerInput := Nat × EncodedSingleCoreRow × Nat
abbrev UniversalInput := Nat × EncodedSingleCoreRow × List Nat

theorem tail_program : Computable (fun p : CompilerInput =>
    singleCorePresburgerTailCode (encodedSingleCoreSupport p.1) (encodedSingleCoreRowSign p.2.1).2++
      singleCorePresburgerConstantCode (decide ((encodedSingleCoreRowSign p.2.1).1=p.2.2))++[(6,0,0)]) := by
  let A := Nat × EncodedSingleCoreRow × Nat
  have hSource : Primrec (fun p : A => p.1) := Primrec.fst
  have hRow : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hDesired : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hSupport := SingleCoreSupport.primitive.comp hSource
  have hSign := SingleCoreRowCompiler.sign_program.comp hRow.to_comp
  have hN := Computable.snd.comp hSign
  have hFlag := Primrec.eq.decide.to_comp.comp (Computable.fst.comp hSign) hDesired.to_comp
  exact (quote_primitive 6).to_comp.comp
    (tail_code_primitive.to_comp.comp hSupport.to_comp hN) (constant_primitive.to_comp.comp hFlag)

theorem numeric_words_program : Computable (fun p : Nat × EncodedSingleCoreRow =>
    singleCoreBoxWords (encodedSingleCoreRowSign p.2).2 (encodedSingleCoreSupport p.1).length) :=
  words_primitive.to_comp.comp (Computable.snd.comp (SingleCoreRowCompiler.sign_program.comp Computable.snd))
    (Primrec.list_length.to_comp.comp (SingleCoreSupport.primitive.to_comp.comp Computable.fst))

theorem box_step_program : Computable₂ (fun p : CompilerInput => fun state : List Nat × List OneInputBooleanInstruction =>
    if encodedSingleCoreBoxSign p.1 p.2.1 state.1=p.2.2 then
      singleCorePresburgerPointCode (encodedSingleCoreSupport p.1) state.1++state.2++[(7,0,0)] else state.2) := by
  have hSource : Primrec (fun p : CompilerInput => p.1) := Primrec.fst
  have hRow : Primrec (fun p : CompilerInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have hDesired : Primrec (fun p : CompilerInput => p.2.2) := Primrec.snd.comp Primrec.snd
  have hSupport := SingleCoreSupport.primitive.comp hSource
  have hBox : Computable (fun p : CompilerInput × (List Nat × List OneInputBooleanInstruction) =>
      encodedSingleCoreBoxSign p.1.1 p.1.2.1 p.2.1) :=
    Computable.comp box_program ((hSource.to_comp.comp Computable.fst).pair
      ((hRow.to_comp.comp Computable.fst).pair (Computable.fst.comp Computable.snd)))
  have hMatch : Computable (fun p : CompilerInput × (List Nat × List OneInputBooleanInstruction) =>
      decide (encodedSingleCoreBoxSign p.1.1 p.1.2.1 p.2.1=p.1.2.2)) :=
    Primrec.eq.decide.to_comp.comp hBox (hDesired.to_comp.comp Computable.fst)
  have hPoint : Computable (fun p : CompilerInput × (List Nat × List OneInputBooleanInstruction) =>
      singleCorePresburgerPointCode (encodedSingleCoreSupport p.1.1) p.2.1) :=
    point_code_primitive.to_comp.comp (hSupport.to_comp.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hKeep : Computable (fun p : CompilerInput × (List Nat × List OneInputBooleanInstruction) =>
      singleCorePresburgerPointCode (encodedSingleCoreSupport p.1.1) p.2.1++p.2.2++[(7,0,0)]) :=
    (quote_primitive 7).to_comp.comp hPoint (Computable.snd.comp Computable.snd)
  have hStep : Computable₂ (fun p : CompilerInput => fun state : List Nat × List OneInputBooleanInstruction =>
      if encodedSingleCoreBoxSign p.1 p.2.1 state.1=p.2.2 then
        singleCorePresburgerPointCode (encodedSingleCoreSupport p.1) state.1++state.2++[(7,0,0)] else state.2) :=
    computable_if hMatch hKeep (Computable.snd.comp Computable.snd)
  exact hStep

theorem box_code_program : Computable (fun p : CompilerInput =>
    (singleCoreBoxWords (encodedSingleCoreRowSign p.2.1).2 (encodedSingleCoreSupport p.1).length).foldr
      (fun word rest => if encodedSingleCoreBoxSign p.1 p.2.1 word=p.2.2 then
        singleCorePresburgerPointCode (encodedSingleCoreSupport p.1) word++rest++[(7,0,0)] else rest)
      (singleCorePresburgerConstantCode false)) :=
  ComparisonAssembly.computable_foldr []
    (numeric_words_program.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
    (Computable.const (singleCorePresburgerConstantCode false)) box_step_program

theorem compiler_program : Computable (fun p : Nat × EncodedSingleCoreRow × Nat =>
    encodedSingleCorePresburger p.1 p.2.1 p.2.2) := by
  apply ((quote_primitive 7).to_comp.comp tail_program box_code_program).of_eq
  intro p
  unfold encodedSingleCorePresburger
  rfl

private theorem membership_primitive : Primrec (fun p : Nat × List Nat => decide (p.1∈p.2)) := by
  have hr : PrimrecRel (fun a b : Nat => a=b) := Primrec.eq
  have h : Primrec (fun p : List Nat × Nat => decide (∃ a∈p.1,a=p.2)) := hr.exists_mem_list.decide
  apply (h.comp (Primrec.snd.pair Primrec.fst)).of_eq
  intro p
  simp

theorem universal_tail_program : Computable (fun p : UniversalInput =>
    (encodedSingleCoreSupport p.1).isEmpty || decide ((encodedSingleCoreRowSign p.2.1).1∈p.2.2)) := by
  let A := Nat × EncodedSingleCoreRow × List Nat
  have hSource : Primrec (fun p : A => p.1) := Primrec.fst
  have hRow : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hAllowed : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hSupport := SingleCoreSupport.primitive.comp hSource
  have hEmpty : Primrec (fun p : A => (encodedSingleCoreSupport p.1).isEmpty) := by
    apply ((Primrec.eq : PrimrecRel (fun a b : List Nat => a=b)).decide.comp hSupport (Primrec.const [])).of_eq
    intro p
    cases encodedSingleCoreSupport p.1 <;> rfl
  have hResult := SingleCoreRowCompiler.sign_program.comp hRow.to_comp
  have hMember : Computable (fun p : A => decide ((encodedSingleCoreRowSign p.2.1).1∈p.2.2)) :=
    Computable.comp membership_primitive.to_comp ((Computable.fst.comp hResult).pair hAllowed.to_comp)
  exact Primrec.or.to_comp.comp hEmpty.to_comp hMember

theorem universal_step_program : Computable₂ (fun p : UniversalInput => fun state : List Nat × Bool =>
    decide (encodedSingleCoreBoxSign p.1 p.2.1 state.1∈p.2.2) && state.2) := by
  have hSource : Primrec (fun p : UniversalInput => p.1) := Primrec.fst
  have hRow : Primrec (fun p : UniversalInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have hAllowed : Primrec (fun p : UniversalInput => p.2.2) := Primrec.snd.comp Primrec.snd
  have hPoint : Computable (fun p : UniversalInput × (List Nat × Bool) => encodedSingleCoreBoxSign p.1.1 p.1.2.1 p.2.1) :=
    Computable.comp box_program ((hSource.to_comp.comp Computable.fst).pair
      ((hRow.to_comp.comp Computable.fst).pair (Computable.fst.comp Computable.snd)))
  have hMember : Computable (fun p : UniversalInput × (List Nat × Bool) =>
      decide (encodedSingleCoreBoxSign p.1.1 p.1.2.1 p.2.1∈p.1.2.2)) :=
    Computable.comp membership_primitive.to_comp (hPoint.pair (hAllowed.to_comp.comp Computable.fst))
  have hStep : Computable₂ (fun p : UniversalInput => fun state : List Nat × Bool =>
      decide (encodedSingleCoreBoxSign p.1 p.2.1 state.1∈p.2.2) && state.2) :=
    Primrec.and.to_comp.comp hMember (Computable.snd.comp Computable.snd)
  exact hStep

theorem universal_all_program : Computable (fun p : UniversalInput =>
    (singleCoreBoxWords (encodedSingleCoreRowSign p.2.1).2 (encodedSingleCoreSupport p.1).length).all
      (fun word => decide (encodedSingleCoreBoxSign p.1 p.2.1 word∈p.2.2))) := by
  have hAll := ComparisonAssembly.computable_foldr []
    (numeric_words_program.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
    (Computable.const true) universal_step_program
  apply hAll.of_eq
  intro p
  generalize singleCoreBoxWords (encodedSingleCoreRowSign p.2.1).2 (encodedSingleCoreSupport p.1).length=words
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [List.foldr_cons,List.all_cons]; rw [ih]

theorem universal_program : Computable (fun p : Nat × EncodedSingleCoreRow × List Nat =>
    encodedSingleCoreUniversal p.1 p.2.1 p.2.2) := by
  apply (Primrec.and.to_comp.comp universal_tail_program universal_all_program).of_eq
  intro p
  unfold encodedSingleCoreUniversal
  rfl

theorem programs : Targets.ActualSingleCorePresburgerPrograms := ⟨compiler_program,universal_program⟩

end LogicLineages.OrdinalComparison.SingleCorePresburger
