module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectionLeafPrimrecProof
open Source NumberedAuxiliaryCoding NumberedExchangeCode NumberedSelfApplication NumberedSelfApplicationPrimrecProof

attribute [local irreducible] Primrec

abbrev Entry (n : Nat) := Ty × Code (Fin n)
abbrev Choice (n : Nat) := (List (Entry n) × List (Entry n)) × (Nat × Ty)

def chooseResult {n : Nat} (p : Choice n) : Option (Code (Fin n)) := do
  let selected ← p.1.1[p.2.1]?
  if selected.1=p.2.2 then pure (applyCode selected.2 p.1.2) else none

theorem chooseResultPrimitive (n : Nat) : Primrec (@chooseResult n) := by
  have ha : Primrec (fun p : Choice n × Entry n => some (applyCode p.2.2 p.1.1.2)) :=
    Primrec.option_some.comp ((applicationPrimitive n).comp
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have hg : Primrec (fun p : Choice n × Entry n =>
      if p.2.1=p.1.2.2 then some (applyCode p.2.2 p.1.1.2) else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) ha (Primrec.const none)
  have h := Primrec.option_bind (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)) hg.to₂
  exact h.of_eq (fun p => by simp only [chooseResult,Option.bind_eq_bind,Option.pure_def])

def bothEntries {n : Nat} (p : Code (Fin n) × Code (Fin n)) : Option (List (Entry n) × List (Entry n)) :=
  (argumentEntries p.1).bind (fun bs => (argumentEntries p.2).map (fun es => (bs,es)))

theorem bothEntriesPrimitive (n : Nat) : Primrec (@bothEntries n) := by
  have hm : Primrec (fun p : (Code (Fin n) × Code (Fin n)) × List (Entry n) =>
      (argumentEntries p.1.2).map (fun es => (p.2,es))) :=
    Primrec.option_map ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  exact Primrec.option_bind ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp Primrec.fst) hm.to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectionLeafPrimrecProof
