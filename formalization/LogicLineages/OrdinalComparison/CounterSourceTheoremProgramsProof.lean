module
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof

private theorem expansion_prim {α : Type} [Primcodable α] (n c : α → Nat)
    (hn : Primrec n) (hc : Primrec c) : Primrec (fun x => CounterLeaderExpansion.threshold (n x) (c x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hc
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hn (Primrec.const 3)))) (Primrec.const 1)

private theorem comparison_prim {α : Type} [Primcodable α] (n c e : α → Nat)
    (hn : Primrec n) (hc : Primrec c) (he : Primrec e) :
    Primrec (fun x => CounterLeaderComparison.threshold (n x) (c x) (e x)) := by
  have hx := expansion_prim n c hn hc
  have hb : Primrec (fun x => 2*c x+10) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hc) (Primrec.const 10)
  have hm : Primrec (fun x => CubicLeaderRecognition.cubicModulus (c x+3) (e x+3)) :=
    Primrec.nat_max.comp (Primrec.const 16) (Primrec.nat_add.comp
      (Primrec.nat_max.comp (Primrec.nat_add.comp hc (Primrec.const 3))
        (Primrec.nat_add.comp he (Primrec.const 3))) (Primrec.const 4))
  exact Primrec.nat_max.comp (Primrec.nat_max.comp hx hb) (Primrec.nat_max.comp hx hm)

private theorem upper_prim {α : Type} [Primcodable α] (n c K : α → Nat)
    (hn : Primrec n) (hc : Primrec c) (hK : Primrec K) : Primrec (fun x => c x+(n x+3)+2*K x+3) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp hc (Primrec.nat_add.comp hn (Primrec.const 3)))
    (Primrec.nat_mul.comp (Primrec.const 2) hK)) (Primrec.const 3)

theorem uniformTailPrograms : Targets.UniformTailPrograms := by
  let A := Nat × Nat × Nat × Nat
  have h1 : Primrec (fun p : A => p.1) := Primrec.fst
  have h2 : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have h3 : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h4 : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  refine ⟨?_,?_,?_⟩
  · exact Primrec.nat_max.comp (comparison_prim _ _ _ h1 h3 h4)
      (comparison_prim _ _ _ h2 h4 h3)
  · have hsum := Primrec.nat_add.comp h2 h1
    exact Primrec.nat_max.comp (expansion_prim _ _ hsum h3) (upper_prim _ _ _ hsum h3 h4)
  · exact Primrec.nat_max.comp (comparison_prim _ _ _ h1 h2 h3)
      (Primrec.nat_max.comp (Primrec.nat_mul.comp (Primrec.const 4) h4)
        (upper_prim _ _ _ h1 h2 h4))

end LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof
