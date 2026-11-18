module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawRosterPrograms
public import LogicLineages.StandardControlCurrent.OrderedOccurrencePermutationPrograms
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm
open OrderedOccurrenceListPrograms
abbrev Input := List Nat × Nat

theorem ties_computable : Computable (fun q : Input => q.1.flatMap fun i =>
    (q.1.filter fun j => j != i).map fun j =>
      (2,q.1.erase i,i,j,WindowCode.matrixSubstitute i (WindowCode.var j) (Code.formula q.2) : Descriptor)) := by
  have perName : Computable₂ (fun q : Input => fun i : Nat =>
      (q.1.filter fun j => j != i).map fun j =>
        (2,q.1.erase i,i,j,WindowCode.matrixSubstitute i (WindowCode.var j) (Code.formula q.2) : Descriptor)) := by
    let A := Input × Nat
    have candidates : Primrec (fun a : A => a.1.1.filter fun j => j != a.2) :=
      filterP (Primrec.fst.comp Primrec.fst)
        ((Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide.not)
    have tuple : Computable₂ (fun a : A => fun j : Nat =>
        (2,a.1.1.erase a.2,a.2,j,WindowCode.matrixSubstitute a.2 (WindowCode.var j) (Code.formula a.1.2) : Descriptor)) := by
      have qs : Computable (fun b : A × Nat => b.1.1.1) := Computable.fst.comp (Computable.fst.comp Computable.fst)
      have i : Computable (fun b : A × Nat => b.1.2) := Computable.snd.comp Computable.fst
      have code : Computable (fun b : A × Nat => Code.formula b.1.1.2) :=
        NormalFormCodeProof.formula_computable.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have sub := WindowCodeProof.matrix_computable.comp
        (code.pair (i.pair (varP.to_comp.comp Computable.snd)))
      exact (Computable.const 2).pair ((eraseP.to_comp.comp (qs.pair i)).pair
        (i.pair (Computable.snd.pair sub)))
    exact mapC 0 candidates.to_comp tuple
  exact flatMapC 0 Computable.fst perName

theorem ordered_computable : Computable (fun q : Input => q.1.permutations.flatMap fun ys =>
    (live q.1 q.2).zipIdx.map fun oi => (3,ys,name oi.1,oi.2,
      WindowCode.conjunction (strictOrder ys) (WindowCode.conjunction
        (maximal (live q.1 q.2) oi.1) (Code.formula q.2)) : Descriptor)) := by
  have perOrder : Computable₂ (fun q : Input => fun ys : List Nat =>
      (live q.1 q.2).zipIdx.map fun oi => (3,ys,name oi.1,oi.2,
        WindowCode.conjunction (strictOrder ys) (WindowCode.conjunction
          (maximal (live q.1 q.2) oi.1) (Code.formula q.2)) : Descriptor)) := by
    let A := Input × List Nat
    have os : Computable (fun a : A => (live a.1.1 a.1.2).zipIdx) :=
      zipIdxP.to_comp.comp (live_primitive.to_comp.comp Computable.fst)
    have tuple : Computable₂ (fun a : A => fun oi : RawOccurrence × Nat =>
      (3,a.2,name oi.1,oi.2,WindowCode.conjunction (strictOrder a.2)
        (WindowCode.conjunction (maximal (live a.1.1 a.1.2) oi.1) (Code.formula a.1.2)) : Descriptor)) := by
      have ys : Computable (fun b : A × (RawOccurrence × Nat) => b.1.2) := Computable.snd.comp Computable.fst
      have o : Computable (fun b : A × (RawOccurrence × Nat) => b.2.1) := Computable.fst.comp Computable.snd
      have k : Computable (fun b : A × (RawOccurrence × Nat) => b.2.2) := Computable.snd.comp Computable.snd
      have os' := live_primitive.to_comp.comp (Computable.fst.comp Computable.fst)
      have code := NormalFormCodeProof.formula_computable.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have matrix := conjunctionP.to_comp.comp (strict_primitive.to_comp.comp ys)
        (conjunctionP.to_comp.comp (maximal_primitive.to_comp.comp (os'.pair o)) code)
      exact (Computable.const 3).pair (ys.pair ((name_primitive.to_comp.comp o).pair (k.pair matrix)))
    exact mapC ((0,0,0,0,0,0,0),0) os tuple
  exact flatMapC [] (OrderedOccurrencePermutationPrograms.permutations_computable.comp Computable.fst) perOrder

theorem dispatch_computable : Computable (fun q : Input => dispatch q.1 q.2) := by
  have code := NormalFormCodeProof.formula_computable.comp (Computable.snd : Computable (fun q : Input => q.2))
  have finished : Computable (fun q : Input => [(0,[],0,0,Code.formula q.2) : Descriptor]) :=
    Primrec.list_cons.to_comp.comp
      ((Computable.const 0).pair ((Computable.const []).pair ((Computable.const 0).pair ((Computable.const 0).pair code)))) (Computable.const [])
  have absent : Computable (fun q : Input => (inactive q.1 q.2).map fun i => (1,q.1,i,0,Code.formula q.2) : List Descriptor) :=
    mapC 0 inactive_primitive.to_comp
      ((Computable.const 1).pair ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair ((Computable.const 0).pair (code.comp Computable.fst)))))
  have empty : PrimrecPred (fun q : Input => q.1=[]) := Primrec.eq.comp Primrec.fst (Primrec.const [])
  have noAbsent : PrimrecPred (fun q : Input => inactive q.1 q.2=[]) :=
    Primrec.eq.comp inactive_primitive (Primrec.const [])
  exact Computable.ite empty.to_comp finished (Computable.ite noAbsent.to_comp
    (Computable.list_append.comp ties_computable ordered_computable) absent)
end LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
