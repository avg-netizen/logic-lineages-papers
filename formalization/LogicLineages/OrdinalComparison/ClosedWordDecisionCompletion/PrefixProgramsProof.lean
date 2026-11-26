module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeDataProgramsProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordNumericProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerDataProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem computable_flatMap {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → β → List σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) := by
  apply (Primrec.list_flatten.to_comp.comp (AlgorithmPrograms.computable_map default hf hg)).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih =>
      simpa only [List.map_cons,List.flatten_cons,List.flatMap_cons] using
        congrArg (fun rest => g a b ++ rest) ih

theorem prefix_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.prefixChildren p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  let B := A × Nat
  have hfloor : Computable (fun p : B × Nat => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hcode : Computable (fun p : B × Nat => p.1.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hx : Computable (fun p : B × Nat => p.1.2) := Computable.snd.comp Computable.fst
  have hn : Computable (fun p : B × Nat => p.1.1.1+p.2) :=
    Primrec.nat_add.to_comp.comp hfloor Computable.snd
  have hinput := hx.pair (hn.pair hcode)
  have hdomains := OriginalWordEvaluation.Proof.Numeric.removedDomainsComputable.comp hinput
  have hvalue := OriginalWordEvaluation.Proof.Numeric.specializeCodeComputable.comp hinput
  have hsome := Computable.option_some.comp (hfloor.pair hvalue)
  have hop : Computable₂ (fun p : B => fun k : Nat =>
      let n := p.1.1+k
      if OriginalWordEvaluation.Code.removedDomains p.2 n p.1.2.2 then
        some (p.1.1,OriginalWordEvaluation.Code.specialize p.2 n p.1.2.2) else none) := by
    apply (Computable.cond hdomains hsome (Computable.const none)).of_eq
    intro p
    dsimp only
    cases OriginalWordEvaluation.Code.removedDomains p.1.2 (p.1.1.1+p.2) p.1.1.2.2 <;> rfl
  have hrange : Computable (fun p : B => List.range (p.1.2.1-p.1.1)) :=
    Primrec.list_range.to_comp.comp (Primrec.nat_sub.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.fst))
  have hinner := RunnerCode.computable_filterMap 0 hrange hop
  have hnames : Computable (fun p : A => Code.names p.2.2) :=
    names_primitive.to_comp.comp (Computable.snd.comp Computable.snd)
  exact computable_flatMap 0 hnames hinner.to₂

#print axioms computable_flatMap
#print axioms prefix_computable

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
