module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxPrimitiveFoldTargets
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntaxPrimitiveFold.Proof
open OrdinalSyntaxComputableFold

/-- The primitive-recursive construction uses the unchanged raw fold equation. -/
theorem exactRawRecursion : Targets.ExactRawRecursion :=
  OrdinalSyntaxComputableFold.Proof.exactRawRecursion

attribute [local irreducible] Nat.unpair Nat.sqrt indexedFold

/-- Jointly primitive-recursive first-order operations induce a joint primitive-recursive fold. -/
theorem indexedPrimitiveRecursive : Targets.IndexedPrimitiveRecursive := by
  intro P A _ _ leaf branch hleaf hbranch
  let children : Nat → List Nat := fun n =>
    if atom n then [] else [(n/8).unpair.1,(n/8).unpair.2]
  let assemble : P → Nat × List A → Option A := fun p nr => some
    (if atom nr.1 then leaf (p,nr.1) else
      branch (p,nr.1%8,(nr.2[0]?).getD (leaf (p,0)),(nr.2[1]?).getD (leaf (p,0))))
  have htag : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hpay : Primrec (fun n : Nat => (n/8).unpair) :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  have hatom : PrimrecPred atom :=
    (Primrec.nat_lt.comp htag (Primrec.const 4)).or (Primrec.eq.comp htag (Primrec.const 7))
  have hc : Primrec children := Primrec.ite hatom (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.fst.comp hpay)
      (Primrec.list_cons.comp (Primrec.snd.comp hpay) (Primrec.const [])))
  have ha : Primrec₂ assemble := by
    have hn : Primrec (fun p : P × (Nat × List A) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hrs : Primrec (fun p : P × (Nat × List A) => p.2.2) := Primrec.snd.comp Primrec.snd
    have hd : Primrec (fun p : P × (Nat × List A) => leaf (p.1,0)) :=
      hleaf.comp (Primrec.fst.pair (Primrec.const 0))
    have hg (k : Nat) : Primrec (fun p : P × (Nat × List A) => (p.2.2[k]?).getD (leaf (p.1,0))) :=
      Primrec.option_getD.comp (Primrec.list_getElem?.comp hrs (Primrec.const k)) hd
    exact Primrec.option_some.comp (Primrec.ite (hatom.comp hn)
      (hleaf.comp (Primrec.fst.pair hn))
      (hbranch.comp (Primrec.fst.pair ((htag.comp hn).pair ((hg 0).pair (hg 1))))))
  apply Primrec.nat_omega_rec (indexedFold leaf branch) Primrec.snd.to₂ (hc.comp Primrec.snd).to₂ ha
  · intro p n k hk
    change k<n
    by_cases h : atom n
    · simp [children,h] at hk
    · have hd := exactRawRecursion.1 n h
      simp only [children,if_neg h,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      · exact hd.1
      · exact hd.2
  · intro p n
    rw [exactRawRecursion.2 P A leaf branch p n]
    by_cases h : atom n <;> simp [children,assemble,h]
end LogicLineages.OrdinalComparison.Source.OrdinalSyntaxPrimitiveFold.Proof
