module
public import LogicLineages.StandardControlCurrent.NumericalKernelRecurrenceProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelProof
open OrdinalComparison NumericalKernel

attribute [local irreducible] Nat.sqrt Nat.unpair encodedNatNote encodedMaximumPredecessor encodedCompensatedCountValue

theorem code_correct (d c t : Nat) (hd : 1 ≤ d) :
    countCode d c t = count d c t ∧ valueCode d c t = value d c t := by
  let eta : NONote := ⟨ONote.ofNat d,ONote.nf_ofNat d⟩
  have hp : 0 < eta.1.repr := by
    simp only [eta,ONote.repr_ofNat]
    exact_mod_cast (by omega : 0 < d)
  have hi := encodedKernelInitialCorrect eta hp 0 0
  have hcode : encodedKernelInitial (rawNoteEncode eta.1) 0 0 = encodedNodeCode (encodedNatNote d) 0 0 := by
    simp only [encodedKernelInitial,Nat.zero_sub,eta]
    rw [encodedNatNoteCorrect d,encodedNatNoteCorrect 0]
    rfl
  rw [hcode] at hi
  let a : NONote := ⟨rawNoteDecode (encodedNodeCode (encodedNatNote d) 0 0),hi.1⟩
  have ha : a.1.repr = Ordinal.omega0 ^ (d : Ordinal) := by
    simpa only [eta,ONote.repr_ofNat,actualSuffixKernelInitial,Nat.zero_sub,Nat.cast_zero,add_zero] using hi.2.1
  have hapos : 0 < a := by
    change 0 < a.1.repr
    rw [ha]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hm := encodedMaximumPredecessorCorrect a hapos (Phi t-c)
  have hv := encodedMaximumPredecessorActualCorrect a hapos (Phi t-c)
  rw [rawNoteEncodeDecode] at hm hv
  have hnf : ONote.NF (rawNoteDecode (encodedMaximumPredecessor (encodedNodeCode (encodedNatNote d) 0 0) (Phi t-c))) := by
    rw [hm,rawNoteDecodeEncode]
    exact (maximumPredecessor a (Phi t-c)).2
  let q : NONote := ⟨_,hnf⟩
  have hc := encodedCompensatedCountCorrect c q
  rw [rawNoteEncodeDecode] at hc
  have hq : q.1.repr = first d c t := by
    change (rawNoteDecode _).repr = _
    rw [hv,ha]
    rfl
  rw [hq] at hc
  have he : countCode d c t = count d c t := by
    unfold countCode count
    rw [hc]
  exact ⟨he,by simp only [valueCode,value,he]⟩

theorem programs : NumericalKernelTargets.Programs := by
  have hn : Primrec (fun x : Nat × Nat × Nat => encodedNodeCode (encodedNatNote x.1) 0 0) :=
    encodedNodeCode_primrec (encodedKernelBuildersPrimitiveRecursive.1.comp Primrec.fst) (Primrec.const 0) (Primrec.const 0)
  have hb : Primrec (fun x : Nat × Nat × Nat => Phi x.2.2-x.2.1) :=
    Primrec.nat_sub.comp (Phi_primrec.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)
  have hm : Computable (fun x : Nat × Nat × Nat => encodedMaximumPredecessor (encodedNodeCode (encodedNatNote x.1) 0 0) (Phi x.2.2-x.2.1)) :=
    encodedMaximumPredecessorPrimitiveRecursive.to_comp.comp hn.to_comp hb.to_comp
  have hc0 : Computable (fun x : Nat × Nat × Nat => encodedCompensatedCountValue x.2.1
      (encodedMaximumPredecessor (encodedNodeCode (encodedNatNote x.1) 0 0) (Phi x.2.2-x.2.1))) :=
    encodedCompensatedCountComputable.comp (Computable.fst.comp Computable.snd) hm
  have hc : Computable (fun x : Nat × Nat × Nat => countCode x.1 x.2.1 x.2.2) :=
    Primrec.nat_add.to_comp.comp (Computable.const 1) hc0
  have hstep : Primrec₂ (fun (_ : Nat × Nat) (x : Nat) => Phi x) := Phi_primrec.comp Primrec.snd
  have hiter : Primrec₂ (fun k t : Nat => (Phi^[k]) t) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd hstep
  have hv : Computable (fun x : Nat × Nat × Nat => valueCode x.1 x.2.1 x.2.2) :=
    hiter.to_comp.comp hc (Computable.snd.comp Computable.snd)
  refine ⟨hc,hv,fun d c t hd _ => code_correct d c t hd,?_⟩
  have ha : Primrec (fun x : Nat × Nat × Int => x.2.2.natAbs) :=
    LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec (fun x : Nat × Nat × Int => x.2.1+2*x.1+1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 1)
  have hright : Primrec (fun x : Nat × Nat × Int => x.2.1+2*x.2.2.natAbs+3) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.const 2) ha)) (Primrec.const 3)
  exact (Primrec.nat_max.comp hleft hright).to_comp
end LogicLineages.StandardControlCurrent.NumericalKernelProof
