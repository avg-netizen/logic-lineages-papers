module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
open LogicLineages.OrdinalComparison.Source
private theorem arrow_primitive : Primrec₂ SyntaxCode.arrowCode :=
  Primrec.nat_add.comp Primrec.natPair (Primrec.const 1)
private theorem case_primitive : Primrec SyntaxCode.caseCode :=
  arrow_primitive.comp (Primrec.const 0)
    (arrow_primitive.comp Primrec.id (arrow_primitive.comp Primrec.id Primrec.id))
private theorem rec_primitive : Primrec SyntaxCode.recCode :=
  arrow_primitive.comp (Primrec.const 0)
    (arrow_primitive.comp
      (arrow_primitive.comp (Primrec.const 0) (arrow_primitive.comp Primrec.id Primrec.id))
      (arrow_primitive.comp Primrec.id Primrec.id))

theorem lookup_primitive : Primrec (fun p : List RawSpec × RawSpec × Nat => lookup p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : List RawSpec × RawSpec × Nat => p.1) := Primrec.fst
  have ht : Primrec (fun p : List RawSpec × RawSpec × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : List RawSpec × RawSpec × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Primrec.nat_lt.comp hi (Primrec.list_length.comp hs)).decide
    (Primrec.eq.comp ((Primrec.list_getD ([],0)).comp hs hi) ht).decide

theorem variable_primitive : Primrec (fun p : List Nat × Nat × Nat => «variable» p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : List Nat × Nat × Nat => p.1) := Primrec.fst
  have ht : Primrec (fun p : List Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : List Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Primrec.nat_lt.comp hi (Primrec.list_length.comp hs)).decide
    (Primrec.eq.comp ((Primrec.list_getD 0).comp hs hi) ht).decide

theorem node_primitive : Primrec (fun p : List Nat × Node × List RawSpec => nodeValid p.1 p.2.1 p.2.2) := by
  let A := List Nat × Node × List RawSpec
  have hg : Primrec (fun p : A => p.1) := Primrec.fst
  have ha : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd := Primrec.fst.comp ha
  have ht := Primrec.fst.comp (Primrec.snd.comp ha)
  have htag := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hargs := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hx := (Primrec.list_getD 0).comp hargs (Primrec.const 0)
  have hy := (Primrec.list_getD 0).comp hargs (Primrec.const 1)
  have hz := (Primrec.list_getD 0).comp hargs (Primrec.const 2)
  have hn := Primrec.list_length.comp hargs
  have h0 := Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 1)).decide
    (variable_primitive.comp ((Primrec.list_append.comp hd hg).pair (ht.pair hx)))
  have h1 := Primrec.and.comp
    (Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 3)).decide
      (lookup_primitive.comp (hs.pair ((hd.pair (arrow_primitive.comp hx ht)).pair hy))))
    (lookup_primitive.comp (hs.pair ((hd.pair hx).pair hz)))
  have h2 := Primrec.and.comp
    (Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 3)).decide
      (Primrec.eq.comp ht (arrow_primitive.comp hx hy)).decide)
    (lookup_primitive.comp (hs.pair (((Primrec.list_cons.comp hx hd).pair hy).pair hz)))
  have h3 := Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 0)).decide
    (Primrec.eq.comp ht (Primrec.const 0)).decide
  have h4 := Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 0)).decide
    (Primrec.eq.comp ht (Primrec.const (SyntaxCode.arrowCode 0 0))).decide
  have h5 := Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 1)).decide
    (Primrec.eq.comp ht (case_primitive.comp hx)).decide
  have h6 := Primrec.and.comp (Primrec.eq.comp hn (Primrec.const 1)).decide
    (Primrec.eq.comp ht (rec_primitive.comp hx)).decide
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) h0
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) h1
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) h2
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) h3
          (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) h4
            (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) h5
              (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) h6 (Primrec.const false))))))

theorem graph_primitive : Primrec (fun p : List Nat × List Node => graph p.1 p.2) := by
  let A := List Nat × List Node
  let S := List RawSpec × Bool
  have hg : Primrec (fun p : A × (Node × S) => p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : A × (Node × S) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : A × (Node × S) => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A × (Node × S) => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have step := (Primrec.list_cons.comp
    ((Primrec.fst.comp ha).pair (Primrec.fst.comp (Primrec.snd.comp ha))) hs).pair
    (Primrec.and.comp hb (node_primitive.comp (hg.pair (ha.pair hs))))
  exact Primrec.list_foldr Primrec.snd (Primrec.const ([],true)) step.to₂

theorem check_primitive : Primrec check := by
  have hg : Primrec (fun c : Code => graph c.1 c.2.1) :=
    graph_primitive.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have ht : Primrec (fun c : Code => c.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun c : Code => c.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.snd.comp hg)
    (lookup_primitive.comp ((Primrec.fst.comp hg).pair (((Primrec.const []).pair ht).pair hi)))
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
