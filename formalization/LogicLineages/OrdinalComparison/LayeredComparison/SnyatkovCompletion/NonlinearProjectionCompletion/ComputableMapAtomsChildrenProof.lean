module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
open ComputableMapAtoms
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
#print axioms tag_primitive

theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
#print axioms quotient_primitive

theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
#print axioms tag_is

theorem children_primitive {α : Type} [Primcodable α] :
    Primrec (children (α := α)) := by
  have hq : Primrec (fun p : Call α => p.2 / 6) :=
    quotient_primitive.comp Primrec.snd
  have hl : Primrec (fun p : Call α => (p.2 / 6).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hq)
  have hr : Primrec (fun p : Call α => (p.2 / 6).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hq)
  exact Primrec.ite (((tag_is 0).or ((tag_is 1).or (tag_is 2))).comp Primrec.snd)
    (Primrec.const [])
    (Primrec.ite ((tag_is 3).comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.pair hq) (Primrec.const []))
      (Primrec.list_cons.comp (Primrec.fst.pair hl)
        (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const []))))
#print axioms children_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
