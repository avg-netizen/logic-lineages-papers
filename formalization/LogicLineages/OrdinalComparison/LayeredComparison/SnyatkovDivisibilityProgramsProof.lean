module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibilityTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionProof
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Proof
open IntegerAlgorithms.Proof CommonHeadCompiler
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem tag_pr : Primrec (fun p : Parameters => p.1) := Primrec.fst
private theorem modulus_pr : Primrec (fun p : Parameters => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem inner_pr : Primrec (fun p : Parameters => p.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem coefficient_pr : Primrec (fun p : Parameters => p.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem outer_pr : Primrec (fun p : Parameters => p.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem cutoff_pr : Primrec cutoff :=
  Primrec.nat_add.comp (Primrec.nat_add.comp modulus_pr (abs_primitive.comp inner_pr))
    (Primrec.const 1)

private theorem term_pr :
    Primrec (fun p : Nat × Nat × Int => termValue p.1 p.2.1 p.2.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Phi_primrec.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (FixedSeedControlResidue.Proof.H_primitive.comp (Primrec.fst.comp Primrec.snd))
      (SnyatkovHyperCollision.Proof.actualPrimitiveRecursion.2.1.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

private theorem affine_test {α : Type} [Primcodable α]
    (m z : α → Nat) (c d : α → Int)
    (hm : Primrec m) (hz : Primrec z) (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun a => decide ((c a * (z a : Int) + d a).natAbs % m a = 0)) :=
  (Primrec.eq.comp
    (Primrec.nat_mod.comp
      (abs_primitive.comp (add_primitive.comp
        (mul_primitive.comp hc (ofNat_primitive.comp hz)) hd)) hm)
    (Primrec.const 0)).decide

private theorem predicate_pr : Primrec₂ predicate :=
  affine_test _ _ _ _ (modulus_pr.comp Primrec.fst)
    (term_pr.comp (Primrec.pair (tag_pr.comp Primrec.fst)
      (Primrec.pair Primrec.snd (inner_pr.comp Primrec.fst))))
    (coefficient_pr.comp Primrec.fst) (outer_pr.comp Primrec.fst)

private theorem tail_pr : Primrec tailBit :=
  affine_test _ _ _ _ modulus_pr
    ((Primrec.nat_mod.comp (fixed_fastControl_primrec 1) Primrec.id).comp modulus_pr) coefficient_pr outer_pr

private theorem small_bits_pr : Primrec smallBits :=
  Primrec.list_map (Primrec.list_range.comp cutoff_pr) predicate_pr

private theorem singleton_pr {α : Type} [Primcodable α]
    (a b c : α → Nat) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun x => ([(a x, b x, c x)] : List Instruction)) :=
  Primrec.list_cons.comp (Primrec.pair ha (Primrec.pair hb hc)) (Primrec.const [])

private theorem variable_pr : Primrec (fun p : Nat × Parameters => 4 * p.1 + 1) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst)
    (Primrec.const 1)

private theorem small_atom_pr :
    Primrec (fun p : (Nat × Parameters) × Nat => smallAtomCode p.1.1 p.1.2 p.2) :=
  Primrec.ite
    (Primrec.eq.comp
      (predicate_pr.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const true))
    (singleton_pr _ _ _ (Primrec.const 2) (variable_pr.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd))
    (Primrec.const [(0, 0, 0)])

attribute [local irreducible] smallAtomCode

private theorem fold_atom_pr :
    Primrec (fun p : (Nat × Parameters) × (Nat × List Instruction) =>
      smallAtomCode p.1.1 p.1.2 p.2.1) := by
  have hp : Primrec (fun p : (Nat × Parameters) × (Nat × List Instruction) =>
      (p.1, p.2.1)) := Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  exact small_atom_pr.comp hp

private theorem small_code_pr : Primrec₂ smallCode := by
  have hs : Primrec (fun p : (Nat × Parameters) × (Nat × List Instruction) =>
      smallAtomCode p.1.1 p.1.2 p.2.1 ++ p.2.2 ++ [(7, 0, 0)]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp fold_atom_pr (Primrec.snd.comp Primrec.snd))
      (Primrec.const [(7, 0, 0)])
  exact Primrec.list_foldr
    (Primrec.list_range.comp (cutoff_pr.comp Primrec.snd))
    (Primrec.const [(0, 0, 0)]) hs.to₂

attribute [local irreducible] smallCode

private theorem formula_code_pr : Primrec₂ formulaCode := by
  have hheader := singleton_pr _ _ _ (Primrec.const 2) variable_pr variable_pr
  have hguard := Primrec.list_append.comp
    (singleton_pr _ _ _ (Primrec.const 3) variable_pr
      (Primrec.nat_mul.comp (Primrec.const 4) (cutoff_pr.comp Primrec.snd)))
    (Primrec.const [(5, 0, 0)])
  have htail : Primrec (fun p : Nat × Parameters =>
      if tailBit p.2 then ([(1, 0, 0)] : List Instruction) else [(0, 0, 0)]) :=
    Primrec.ite (Primrec.eq.comp (tail_pr.comp Primrec.snd) (Primrec.const true))
      (Primrec.const [(1, 0, 0)]) (Primrec.const [(0, 0, 0)])
  apply (Primrec.list_append.comp hheader
    (Primrec.list_append.comp small_code_pr
      (Primrec.list_append.comp hguard
        (Primrec.list_append.comp htail
          (Primrec.const [(6, 0, 0), (7, 0, 0), (6, 0, 0)]))))).of_eq
  intro p
  simp only [formulaCode, List.append_assoc, List.cons_append, List.nil_append]

theorem actualPrimitiveRecursion : Targets.ActualPrimitiveRecursion :=
  ⟨cutoff_pr, predicate_pr, tail_pr, small_bits_pr, formula_code_pr⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Proof
