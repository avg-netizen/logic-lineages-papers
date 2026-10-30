module
public import LogicLineages.OrdinalComparison.EncodedKernelWordTargets
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem word_rec_iterate {α : Type} (f : α → α) (x : α) (n : Nat) :
    Nat.rec x (fun _ y => f y) n=(f^[n]) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (Nat.rec x (fun _ y => f y) n)=(f^[n+1]) x
    rw [ih,Function.iterate_succ_apply']

theorem encodedKernelWordComputable : Targets.EncodedKernelWordComputable := by
  let S := List (Nat × Nat) × (Nat × Nat)
  have hh : Computable (fun s : S => s.1.getD 0 (0,0)) :=
    (Primrec.list_getD (0,0)).to_comp.comp Computable.fst (Computable.const 0)
  have hi : Computable (fun s : S => ((s.1.getD 0 (0,0)).1,((s.1.getD 0 (0,0)).2,s.2.1))) :=
    (Computable.fst.comp hh).pair ((Computable.snd.comp hh).pair (Computable.fst.comp Computable.snd))
  have hK := encodedSuffixKernelComputable.2.comp hi
  have hE := encodedSuffixKernelComputable.1.comp hi
  have hstep : Computable encodedKernelWordStep :=
    ((Primrec.list_tail.to_comp).comp Computable.fst).pair
      (hK.pair (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) hE))
  have hlen : Computable (fun p : List (Nat × Nat) × Nat => p.1.length) :=
    Computable.list_length.comp Computable.fst
  have hinit : Computable (fun p : List (Nat × Nat) × Nat => (p.1,(p.2,0))) :=
    Computable.fst.pair (Computable.snd.pair (Computable.const 0))
  have hbody : Computable₂ (fun (_ : List (Nat × Nat) × Nat) (q : Nat × S) => encodedKernelWordStep q.2) :=
    hstep.comp (Computable.snd.comp Computable.snd)
  have hrec := Computable.nat_rec hlen hinit hbody
  have hrun : Computable (fun p : List (Nat × Nat) × Nat =>
      (encodedKernelWordStep^[p.1.length]) (p.1,(p.2,0))) :=
    hrec.of_eq (fun p => word_rec_iterate encodedKernelWordStep (p.1,(p.2,0)) p.1.length)
  exact Computable.snd.comp hrun

private theorem encoded_word_acc (w : List (ONote × Nat))
    (hv : ∀ p ∈ w, ONote.NF p.1 ∧ 0<p.1.repr) :
    ∀ t : Nat, actualPrincipalWordGenuine w t → ∀ acc : Nat,
      (encodedKernelWordStep^[w.length]) (encodePrincipalKernelWord w,(t,acc))=
        ([],((actualPrincipalWordRun w t).1,acc+(actualPrincipalWordRun w t).2)) := by
  induction w with
  | nil => intro t _ acc; simp [encodePrincipalKernelWord,actualPrincipalWordRun]
  | cons p w ih =>
    intro t hg acc
    have hp := hv p (by simp)
    have hw : ∀ q ∈ w, ONote.NF q.1 ∧ 0<q.1.repr := by intro q hq; exact hv q (by simp [hq])
    let eta : NONote := ⟨p.1,hp.1⟩
    have hc := encodedSuffixKernelCorrect eta hp.2 p.2 t hg.1
    have hstep : encodedKernelWordStep (encodePrincipalKernelWord (p::w),(t,acc))=
        (encodePrincipalKernelWord w,(actualSuffixKernel (Ordinal.omega0^p.1.repr) p.2 t,
          acc+actualSuffixKernelCount (Ordinal.omega0^p.1.repr) p.2 t)) := by
      simp only [encodedKernelWordStep,encodePrincipalKernelWord,List.map_cons,List.getD_cons_zero,List.tail_cons]
      rw [hc.1,hc.2]
    change (encodedKernelWordStep^[w.length+1]) (encodePrincipalKernelWord (p::w),(t,acc))=_
    rw [Function.iterate_succ_apply,hstep,ih hw _ hg.2]
    simp only [actualPrincipalWordRun,Nat.add_assoc]

theorem encodedKernelWordCorrect : Targets.EncodedKernelWordCorrect := by
  intro w hv t hg
  have h := congrArg Prod.snd (encoded_word_acc w hv t hg 0)
  simpa only [encodedKernelWordRun,encodePrincipalKernelWord,List.length_map,Nat.zero_add] using h

end LogicLineages.OrdinalComparison
