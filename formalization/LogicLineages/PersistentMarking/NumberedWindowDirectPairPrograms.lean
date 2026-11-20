module

public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectPairPrograms
open LogicLineages.ComputabilityKnowledge List.Vector

private theorem polynomial : Primrec (fun p : Nat × Nat => NumberedWindowPairAlgorithm.pair p.1 p.2) := by
  have sum := Primrec.nat_add.comp Primrec.fst Primrec.snd
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp sum sum) Primrec.fst

private theorem rows : Primrec (fun p : Nat × Nat => (List.range (p.1+1)).map (fun b => (p.2,b))) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

private theorem search : Primrec NumberedWindowPairAlgorithm.decode := by
  have candidates : Primrec NumberedWindowPairAlgorithm.candidates :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) rows.to₂
  have test : Primrec (fun p : Nat × Nat × Nat => decide (NumberedWindowPairAlgorithm.pair p.2.1 p.2.2 = p.1)) :=
    (Primrec.eq.comp (polynomial.comp Primrec.snd) Primrec.fst).decide
  have index := Primrec.list_findIdx candidates test.to₂
  exact (Primrec.list_getElem?.comp candidates index).of_eq (fun _ => List.find?_eq_getElem?_findIdx.symm)

theorem encoding (f : Nat → Nat → Nat) (h : f = NumberedWindowPairAlgorithm.pair) :
    ∃ p : GorbowPRProgram.Program 2, ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = f a b := by
  subst f
  let g := fun v : List.Vector Nat 2 => NumberedWindowPairAlgorithm.pair v.head v.tail.head
  have prim : Primrec g := polynomial.comp (Primrec.vector_head.pair (Primrec.vector_head.comp Primrec.vector_tail))
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 g prim
  exact ⟨p,fun a b => hp (a ::ᵥ b ::ᵥ List.Vector.nil)⟩

theorem decoding (f : Nat → Option (Nat × Nat)) (h : f = NumberedWindowPairAlgorithm.decode) :
    ∃ p : GorbowPRProgram.Program 1, ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (f n) := by
  subst f
  exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp search)

end LogicLineages.PersistentMarking.NumberedWindowDirectPairPrograms
