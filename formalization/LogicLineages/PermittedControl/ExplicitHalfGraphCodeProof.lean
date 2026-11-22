module
public import LogicLineages.PermittedControl.ExplicitHalfGraphTargets
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ExplicitHalfGraph
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem atomPrimitive (c d : Int) : Primrec (fun p : Nat × Nat =>
    6 * Encodable.encode ((0,0,0,[(c,(0,p.1,0,0)),(d,(0,p.2,0,0))]) : NormalForm.Code.AtomData) + 2) := by
  let Args := Nat × Nat
  have firstName : Primrec (fun p : Args => (0,p.1,0,0)) :=
    (Primrec.const 0).pair (Primrec.fst.pair (Primrec.const (0,0)))
  have secondName : Primrec (fun p : Args => (0,p.2,0,0)) :=
    (Primrec.const 0).pair (Primrec.snd.pair (Primrec.const (0,0)))
  have tail := Primrec.list_cons.comp ((Primrec.const d).pair secondName) (Primrec.const [])
  have row := Primrec.list_cons.comp ((Primrec.const c).pair firstName) tail
  have data : Primrec (fun p : Args =>
      ((0,0,0,[(c,(0,p.1,0,0)),(d,(0,p.2,0,0))]) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const (0 : Int)).pair row))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp data)) (Primrec.const 2)

theorem codeExact : CodeExact := by
  have swap : Primrec (fun p : Nat × Nat => (p.2,p.1)) := Primrec.snd.pair Primrec.fst
  have flipped := (atomPrimitive 2 (-1)).comp swap
  have atLeast : Primrec (fun p : Nat × Nat => 6 * Encodable.encode (atLeastData p.1 p.2) + 2) :=
    flipped.of_eq (fun _ => rfl)
  have atMost : Primrec (fun p : Nat × Nat => 6 * Encodable.encode (atMostData p.1 p.2) + 2) :=
    (atomPrimitive 1 (-2)).of_eq (fun _ => rfl)
  have pair := Primrec₂.natPair.comp atLeast atMost
  have code := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) pair) (Primrec.const 4)
  refine ⟨(code.of_eq (fun p : Nat × Nat => show _ = graphCode p.1 p.2 from rfl)).to₂,?_⟩
  intro full half
  rfl

end LogicLineages.PermittedControl.ExplicitHalfGraph
