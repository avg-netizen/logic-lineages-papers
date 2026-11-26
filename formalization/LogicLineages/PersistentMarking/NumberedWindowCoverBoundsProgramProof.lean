module

public import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowCoverProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowCoverBoundsAlgorithm
open NumberedWindowCoverBoundsProgramTargets NumberedWindowFieldAlgorithm List.Vector

private theorem choose {α} [Primcodable α] {tag : α → Nat} (ht : Primrec tag)
    (n : Nat) {f g : α → Measure} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if tag a = n then f a else g a) :=
  Primrec.ite (Primrec.eq.comp ht (Primrec.const n)) hf hg

private theorem measurePrim : Primrec (fun p : List Measures × Nat × List Nat =>
    termMeasure p.1 p.2.1 p.2.2) := by
  let P := List Measures × Nat × List Nat
  let val (i : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : P → _))) (Primrec.const i)
  let entry (i : Nat) := (Primrec.list_getD (default : Measures)).comp Primrec.fst (val i)
  let tm (i : Nat) := Primrec.fst.comp (entry i)
  let ar (i : Nat) := Primrec.snd.comp (entry i)
  let above {f : P → Measure} (h : Primrec f) := (Primrec.succ.comp (Primrec.fst.comp h)).pair (Primrec.snd.comp h)
  let both {f g : P → Measure} (h : Primrec f) (j : Primrec g) :=
    Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp h) (Primrec.fst.comp j))
  let height {f g : P → Measure} (h : Primrec f) (j : Primrec g) :=
    Primrec.nat_max.comp (Primrec.snd.comp h) (Primrec.snd.comp j)
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  let variableMeasure := (Primrec.const 1).pair (val 1)
  let num := (both (ar 3) (ar 4)).pair (Primrec.nat_max.comp (val 2) (height (ar 3) (ar 4)))
  let app := (both (tm 2) (tm 3)).pair (height (tm 2) (tm 3))
  apply (choose tag 0 variableMeasure (choose tag 1 variableMeasure (choose tag 2 (above (tm 1))
    (choose tag 3 (Primrec.const (1,0)) (choose tag 4 (above (ar 1)) (choose tag 5 num
      (choose tag 6 app (Primrec.const (0,0))))))))).of_eq
  rintro ⟨t,tag,xs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n <;> simp [termMeasure]

private theorem termNextPrim : Primrec₂ termNext := by
  have node : Primrec unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact Primrec.option_getD.comp (Primrec.option_map (node.comp Primrec.fst)
    (measurePrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂) (Primrec.const default)

private theorem argsNextPrim : Primrec₂ argsNext := by
  let check (p : List Measures × Nat) := ((NumberedWindowPairAlgorithm.decode p.2).map (fun qr =>
    let q := (p.1.getD qr.1 default).1
    let r := (p.1.getD qr.2 default).2
    (q.1+1+r.1,max q.2 r.2))).getD default
  have prev : Primrec (fun p : (List Measures × Nat) × Nat × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have q := Primrec.fst.comp ((Primrec.list_getD (default : Measures)).comp prev (Primrec.fst.comp Primrec.snd))
  have r := Primrec.snd.comp ((Primrec.list_getD (default : Measures)).comp prev (Primrec.snd.comp Primrec.snd))
  have pairMeasure := (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.fst.comp q)) (Primrec.fst.comp r)).pair
    (Primrec.nat_max.comp (Primrec.snd.comp q) (Primrec.snd.comp r))
  have test : Primrec check := Primrec.option_getD.comp
    (Primrec.option_map (NumberedWindowSyntaxShapePrograms.pairs.comp Primrec.snd) pairMeasure.to₂) (Primrec.const default)
  apply (Primrec.nat_casesOn Primrec.fst (Primrec.const (0,0))
    (test.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
  rintro ⟨n,prev⟩
  cases n <;> rfl

theorem metrics : Primrec bounds := by
  have next : Primrec (fun p : Nat × List Measures => (termNext p.1 p.2,argsNext p.1 p.2)) :=
    Primrec.pair termNextPrim argsNextPrim
  have step : Primrec₂ (fun n (xs : List Measures) => xs ++ [(termNext n xs,argsNext n xs)]) :=
    Primrec.list_append.comp Primrec.snd (Primrec.list_cons.comp next (Primrec.const []))
  have tables : Primrec table := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [table,ih])
  exact next.comp (Primrec.id.pair tables)

theorem measureProgram : MeasureProgram :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp metrics)

private def readList (n : Nat) := ((Encodable.decode n : Option (List Nat)).getD [])
private theorem readListPrim : Primrec readList := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem selectedProgram : SelectedCoverProgram := by
  let V := List.Vector Nat 3
  have H : Primrec (fun v : V => readList v.head) := readListPrim.comp Primrec.vector_head
  have K := readListPrim.comp (Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have n := Primrec.vector_head.comp (Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have b := Primrec.fst.comp (metrics.comp n)
  have grammar := NumberedWindowCoverProgramProof.grammarPrim.comp
    (H.pair (K.pair (Primrec.snd.comp b))) (Primrec.fst.comp b)
  have ok := Primrec.fst.comp (NumberedWindowSyntaxProgramProof.bits.comp n)
  have selected : Primrec (fun v : V => cover (readList v.head) (readList v.tail.head) v.tail.tail.head) := by
    apply (Primrec.cond ok (Primrec.option_some.comp (Primrec.fst.comp grammar)) (Primrec.const none)).of_eq
    intro v
    cases h : (NumberedWindowSyntaxAlgorithm.syntaxBits v.tail.tail.head).1 <;> simp [cover,h]
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (Primrec.encode.comp selected)
  exact ⟨p,fun H K n => by simpa [readList] using eval (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramProof
