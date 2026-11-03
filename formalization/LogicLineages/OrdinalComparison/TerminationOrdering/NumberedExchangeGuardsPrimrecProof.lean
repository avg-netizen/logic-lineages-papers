module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecTargets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedHeadCodecPrimrec
open NumberedHeadCodecPrimrecSupportProof

def headClassNumber {n : Nat} : HeadCode (Fin n) → Nat
  | .zero | .succ | .cases _ | .recursor _ => 0
  | .application _ _ => 1
  | .ranked s => 2 + s.val

theorem headClassNumberPrimitive (n : Nat) : Primrec (@headClassNumber n) := by
  have h : Primrec (fun data : HeadData n => data.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 1) (fun s => 2 + s.val))))) :=
    sumElim (Primrec.const 0) (sumElim (Primrec.const 0)
      (sumElim (Primrec.const 0) (sumElim (Primrec.const 1)
        (Primrec.nat_add.comp (Primrec.const 2) Primrec.fin_val))))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

theorem headClassNumberCalibration {n : Nat} (f g : HeadCode (Fin n)) :
    headClassNumber f = headClassNumber g ↔
      RecursiveComparison.headEquivalent (decodeHead f) (decodeHead g) := by
  cases f <;> cases g <;>
    simp [headClassNumber, decodeHead, RecursiveComparison.headEquivalent,
      RecursiveComparison.headClass, Fin.ext_iff] <;> omega

theorem headEquivalencePrimitive :
    NumberedExchangeGuardsPrimrecTargets.ActualHeadEquivalencePrimitive := by
  intro n
  have h : PrimrecPred (fun p : HeadCode (Fin n) × HeadCode (Fin n) =>
      headClassNumber p.1 = headClassNumber p.2) :=
    Primrec.eq.comp ((headClassNumberPrimitive n).comp Primrec.fst)
      ((headClassNumberPrimitive n).comp Primrec.snd)
  exact (h.of_eq (fun p => headClassNumberCalibration p.1 p.2)).decide

theorem countPrimitive (A : Type) [Primcodable A] [DecidableEq A] :
    Primrec₂ (fun (a : A) (xs : List A) => xs.count a) := by
  have hstep : Primrec (fun p : (A × List A) × (A × Nat) =>
      if p.2.1 = p.1.1 then p.2.2 + 1 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have h : Primrec (fun p : A × List A =>
      p.2.foldr (fun b total => if b = p.1 then total + 1 else total) 0) :=
    Primrec.list_foldr Primrec.snd (Primrec.const 0) hstep.to₂
  apply h.to₂.of_eq
  intro a xs
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases hba : b = a <;> simp [List.count_cons, hba, ih, beq_iff_eq, Nat.add_comm]

theorem permutationPrimitive (A : Type) [Primcodable A] [DecidableEq A] :
    Primrec (fun p : List A × List A => decide (p.1.Perm p.2)) := by
  have hcounts : PrimrecRel (fun (a : A) (p : List A × List A) =>
      p.1.count a = p.2.count a) :=
    Primrec.eq.comp
      ((countPrimitive A).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      ((countPrimitive A).comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  have hbounded : PrimrecPred (fun p : List A × List A =>
      ∀ a ∈ p.1 ++ p.2, p.1.count a = p.2.count a) :=
    hcounts.forall_mem_list.comp (Primrec.list_append.comp Primrec.fst Primrec.snd) Primrec.id
  apply (hbounded.of_eq ?_).decide
  intro p
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro a
    by_cases ha : a ∈ p.1 ++ p.2
    · exact h a ha
    · have hleft : a ∉ p.1 := fun h => ha (List.mem_append_left _ h)
      have hright : a ∉ p.2 := fun h => ha (List.mem_append_right _ h)
      simp [List.count_eq_zero_of_not_mem hleft, List.count_eq_zero_of_not_mem hright]
  · intro h a _
    exact List.perm_iff_count.mp h a

theorem argumentPermutationPrimitive :
    NumberedExchangeGuardsPrimrecTargets.ActualPermutationPrimitive := by
  intro n
  exact permutationPrimitive (Ty × Code (Fin n))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
