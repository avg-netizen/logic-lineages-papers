module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsChildrenProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
open ComputableMapAtoms
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem computable_ite {α β : Type} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg
#print axioms computable_ite

theorem assemble_computable {α : Type} [Primcodable α]
    {op : α → Nat → Nat} (hop : Computable₂ op) :
    Computable₂ (assemble op) := by
  let C := Call α × List Nat
  have hc : Primrec (fun p : C => p.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Computable (fun p : C => p.1.1) :=
    (Primrec.fst.comp Primrec.fst).to_comp
  have h0 : Primrec (fun p : C => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : C => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  have hu (n : Nat) : Primrec (fun k : Nat => 6 * k + n) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
      (Primrec.const n)
  have hatom : Computable (fun p : C => 6 * op p.1.1 (p.1.2 / 6) + 2) :=
    (hu 2).to_comp.comp (hop.comp ha (quotient_primitive.comp hc).to_comp)
  have hnegative : Primrec (fun p : C => 6 * p.2.getD 0 0 + 3) :=
    (hu 3).comp h0
  have hbinary : Primrec (fun p : C =>
      6 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + p.1.2 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1))
      (tag_primitive.comp hc)
  change Computable (fun p : C => assemble op p.1 p.2)
  unfold assemble
  exact computable_ite ((tag_is 0).comp hc) (Computable.const 0)
    (computable_ite ((tag_is 1).comp hc) (Computable.const 1)
      (computable_ite ((tag_is 2).comp hc) hatom
        (computable_ite ((tag_is 3).comp hc) hnegative.to_comp hbinary.to_comp)))
#print axioms assemble_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
