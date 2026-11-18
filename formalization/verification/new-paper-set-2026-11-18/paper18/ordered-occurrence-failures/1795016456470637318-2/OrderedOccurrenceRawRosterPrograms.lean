module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawRowsPrograms
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceListPrograms
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm
open OrderedOccurrenceListPrograms

theorem roster_primitive : Primrec roster := by
  have perRow : Primrec (fun ri : Code.RowData × Nat => ri.1.2.zipIdx.map
      (fun ai => (ri.2,ai.2,ai.1.1,ai.1.2) : RawOccurrence)) :=
    Primrec.list_map (zipIdxP.comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair
          ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
  exact Primrec.list_flatMap (zipIdxP.comp rows_primitive) (perRow.comp Primrec.snd)

theorem name_primitive : Primrec name := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd)))
theorem term_primitive : Primrec term :=
  NormalFormCodeProof.itemTerm_primitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem live_primitive : Primrec (fun q : List Nat × Nat => live q.1 q.2) := by
  have test : Primrec₂ (fun q : List Nat × Nat => fun o : RawOccurrence =>
      o.2.2.1 != 0 && o.2.2.2.1 != 0 && name o ∈ q.1) := by
    have c := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have tag := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hc := (Primrec.eq.comp c (Primrec.const (0 : Int))).decide.not
    have ht := (Primrec.eq.comp tag (Primrec.const (0 : Nat))).decide.not
    exact (hc.and ht).and (memberP.comp ((name_primitive.comp Primrec.snd).pair (Primrec.fst.comp Primrec.fst)))
  exact filterP (roster_primitive.comp Primrec.snd) test

theorem inactive_primitive : Primrec (fun q : List Nat × Nat => inactive q.1 q.2) := by
  have test : Primrec₂ (fun q : List Nat × Nat => fun i : Nat =>
      !(live q.1 q.2).any (fun o => name o == i)) := by
    have ha := anyP (live_primitive.comp Primrec.fst)
      ((Primrec.eq.comp (name_primitive.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).decide)
    exact ha.not
  exact filterP Primrec.fst test

def binaryCode (base tag : Nat) (a b : Nat) := base*Nat.pair a b+tag
theorem binaryP (base tag : Nat) : Primrec₂ (binaryCode base tag) :=
  (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair).add (Primrec.const tag)
theorem varP : Primrec WindowCode.var := (Primrec.nat_mul.comp (Primrec.const 10) Primrec.id).add (Primrec.const 1)
theorem lessP : Primrec₂ WindowCode.less := binaryP 8 3
theorem conjunctionP : Primrec₂ WindowCode.conjunction := binaryP 8 6
theorem atMostP : Primrec₂ WindowCode.atMost :=
  (Primrec.nat_mul.comp (Primrec.const 8) (lessP.comp Primrec.snd Primrec.fst)).add (Primrec.const 5)

theorem all_primitive : Primrec all :=
  Primrec.list_foldr Primrec.id (Primrec.const 0) (conjunctionP.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem strict_primitive : Primrec strictOrder := by
  have perName : Primrec₂ (fun xs : List Nat => fun xi : Nat × Nat =>
      (xs.drop (xi.2+1)).map (fun j => WindowCode.less (WindowCode.var j) (WindowCode.var xi.1))) :=
    Primrec.list_map
      (Primrec.list_drop.comp ((Primrec.snd.comp Primrec.snd).add (Primrec.const 1)) Primrec.fst)
      (lessP.comp (varP.comp Primrec.snd)
        (varP.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  exact all_primitive.comp (Primrec.list_flatMap zipIdxP perName)

theorem maximal_primitive : Primrec (fun q : List RawOccurrence × RawOccurrence => maximal q.1 q.2) :=
  all_primitive.comp (Primrec.list_map Primrec.fst
    (atMostP.comp (term_primitive.comp Primrec.snd) (term_primitive.comp (Primrec.snd.comp Primrec.fst))))
end LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
