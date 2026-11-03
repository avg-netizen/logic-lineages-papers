module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedAuxiliaryEnumeration
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedCodeView NumberedExchangeCode
open NumberedHeadCodecPrimrecSupportProof

private abbrev Entries (n : Nat) := List (Ty × Code (Fin n))
private abbrev Values (n : Nat) := List (Option (Entries n))

private def entryHead {Symbol : Type} : Code Symbol → Option (Ty × Code Symbol)
  | .argumentsCons tau q _ => some (tau, q)
  | _ => none

private def entryHeadView (n : Nat) : CodeView n → Option (Ty × Code (Fin n)) :=
  Sum.elim (fun _ : Nat => none)
    (Sum.elim (fun _ : Ty × Code (Fin n) => none)
      (Sum.elim (fun _ : Ty × Code (Fin n) × Code (Fin n) => none)
        (Sum.elim (fun _ : Ty => none)
          (Sum.elim (fun _ : HeadCode (Fin n) × Code (Fin n) => none)
            (Sum.elim
              (fun _ : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) => none)
              (Sum.elim (fun _ : Unit => none)
                (fun p : Ty × Code (Fin n) × Code (Fin n) => some (p.1, p.2.1))))))))

private theorem entryHeadViewPrimitive (n : Nat) : Primrec (entryHeadView n) := by
  unfold entryHeadView
  apply sumElim (Primrec.const none)
  apply sumElim (Primrec.const none)
  apply sumElim (Primrec.const none)
  apply sumElim (Primrec.const none)
  apply sumElim (Primrec.const none)
  apply sumElim (Primrec.const none)
  exact sumElim (Primrec.const none)
    (Primrec.option_some.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))

private theorem entryHeadPrimitive (n : Nat) : Primrec (@entryHead (Fin n)) :=
  ((entryHeadViewPrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
    (by intro code; cases code <;> rfl)

/-- The accepted child list places the argument tail at index one. -/
private def entriesRecombine {n : Nat} (code : Code (Fin n)) (values : Values n) :
    Option (Option (Entries n)) :=
  some (if code = .argumentsNil then some [] else
    (entryHead code).bind fun entry =>
      (values.getD 1 none).map (fun entries => entry :: entries))

private theorem entriesRecombinePrimitive (n : Nat) : Primrec₂ (@entriesRecombine n) := by
  have htail : Primrec (fun p : (Code (Fin n) × Values n) × (Ty × Code (Fin n)) =>
      p.1.2.getD 1 none) :=
    (Primrec.list_getD (none : Option (Entries n))).comp
      (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
  have hcons : Primrec (fun p : ((Code (Fin n) × Values n) × (Ty × Code (Fin n))) × Entries n =>
      p.1.2 :: p.2) :=
    Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hmap : Primrec (fun p : (Code (Fin n) × Values n) × (Ty × Code (Fin n)) =>
      (p.1.2.getD 1 none).map (fun entries => p.2 :: entries)) :=
    Primrec.option_map htail hcons.to₂
  have hbind : Primrec (fun p : Code (Fin n) × Values n =>
      (entryHead p.1).bind fun entry =>
        (p.2.getD 1 none).map (fun entries => entry :: entries)) :=
    Primrec.option_bind ((entryHeadPrimitive n).comp Primrec.fst) hmap.to₂
  exact (Primrec.option_some.comp
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const (Code.argumentsNil : Code (Fin n))))
      (Primrec.const (some ([] : Entries n))) hbind)).to₂

private theorem entriesRecombineCalibration (n : Nat) (code : Code (Fin n)) :
    entriesRecombine code
      ((NumberedSyntaxBoundsPrimrecSupportProof.children code).map argumentEntries) =
        some (argumentEntries code) := by
  cases code <;> simp [entriesRecombine, entryHead,
    NumberedSyntaxBoundsPrimrecSupportProof.children, argumentEntries]

theorem argumentEntriesPrimitive (n : Nat) : Primrec (@argumentEntries (Fin n)) :=
  Primrec.nat_omega_rec' (@argumentEntries (Fin n))
    (m := @codeNumber n) (l := @NumberedSyntaxBoundsPrimrecSupportProof.children (Fin n))
    (g := @entriesRecombine n)
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n)
    (NumberedSyntaxBoundsPrimrecSupportProof.childrenPrimitive n)
    (entriesRecombinePrimitive n)
    (NumberedSyntaxBoundsPrimrecSupportProof.childrenDecrease n)
    (entriesRecombineCalibration n)

private def entriesPermutation {n : Nat} (p : Option (Entries n) × Option (Entries n)) : Bool :=
  Option.casesOn p.1 false (fun source =>
    Option.casesOn p.2 false (fun result => decide (source.Perm result)))

private theorem entriesPermutationPrimitive (n : Nat) : Primrec (@entriesPermutation n) := by
  have hright : Primrec (fun p : (Option (Entries n) × Option (Entries n)) × Entries n =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have hperm : Primrec (fun p : ((Option (Entries n) × Option (Entries n)) × Entries n) × Entries n =>
      decide (p.1.2.Perm p.2)) :=
    (NumberedExchangeGuardsPrimrecProof.argumentPermutationPrimitive n).comp
      (g := fun p : ((Option (Entries n) × Option (Entries n)) × Entries n) × Entries n =>
        (p.1.2, p.2))
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hrightCase : Primrec (fun p : (Option (Entries n) × Option (Entries n)) × Entries n =>
      (Option.casesOn p.1.2 false (fun entries : Entries n => decide (p.2.Perm entries)) : Bool)) :=
    Primrec.option_casesOn
      (o := fun p : (Option (Entries n) × Option (Entries n)) × Entries n => p.1.2)
      (f := fun _ : (Option (Entries n) × Option (Entries n)) × Entries n => false)
      (g := fun (p : (Option (Entries n) × Option (Entries n)) × Entries n)
        (entries : Entries n) => decide (p.2.Perm entries))
      hright (Primrec.const false) hperm.to₂
  exact Primrec.option_casesOn
    (o := fun p : Option (Entries n) × Option (Entries n) => p.1)
    (f := fun _ : Option (Entries n) × Option (Entries n) => false)
    (g := fun (p : Option (Entries n) × Option (Entries n)) (source : Entries n) =>
      (Option.casesOn p.2 false (fun result : Entries n => decide (source.Perm result)) : Bool))
    Primrec.fst (Primrec.const false) hrightCase.to₂

theorem argumentPermutationPrimitive (n : Nat) :
    Primrec₂ (@argumentPermutation (Fin n) inferInstance) := by
  have hleft : Primrec (fun p : Code (Fin n) × Code (Fin n) => argumentEntries p.1) :=
    (argumentEntriesPrimitive n).comp
      (g := fun p : Code (Fin n) × Code (Fin n) => p.1) Primrec.fst
  have hright : Primrec (fun p : Code (Fin n) × Code (Fin n) => argumentEntries p.2) :=
    (argumentEntriesPrimitive n).comp
      (g := fun p : Code (Fin n) × Code (Fin n) => p.2) Primrec.snd
  have h : Primrec (fun p : Code (Fin n) × Code (Fin n) =>
      entriesPermutation (argumentEntries p.1, argumentEntries p.2)) :=
    (entriesPermutationPrimitive n).comp
      (g := fun p : Code (Fin n) × Code (Fin n) =>
        (argumentEntries p.1, argumentEntries p.2)) (hleft.pair hright)
  apply h.to₂.of_eq
  intro base target
  unfold entriesPermutation argumentPermutation
  cases argumentEntries base <;> cases argumentEntries target <;> rfl

private abbrev HeadMoveInput (n : Nat) :=
  (List (Fin n) × List Ty) ×
    (HeadCode (Fin n) × Code (Fin n)) × (HeadCode (Fin n) × Code (Fin n))

theorem headMovePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : (List (Fin n) × List Ty) ×
        (HeadCode (Fin n) × Code (Fin n)) × (HeadCode (Fin n) × Code (Fin n)) =>
      headMove arity p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hf : Primrec (fun p : HeadMoveInput n => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hg : Primrec (fun p : HeadMoveInput n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p : HeadMoveInput n => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have htarget : Primrec (fun p : HeadMoveInput n => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hwindow : Primrec (fun p : HeadMoveInput n =>
      decide (HeadInWindow arity p.1.1 p.1.2 (decodeHead p.2.1.1))) :=
    (NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
      (g := fun p : HeadMoveInput n => (p.1.1, p.1.2, p.2.1.1))
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair hf))
  have hheads : Primrec (fun p : HeadMoveInput n => sourceHeads arity p.1.1 p.1.2) :=
    (NumberedEnumerationOperationsPrimrecProof.sourceHeadsPrimitive n arity).comp
      (g := fun p : HeadMoveInput n => p.1) Primrec.fst
  have hmember : Primrec (fun p : HeadMoveInput n =>
      decide (p.2.2.1 ∈ sourceHeads arity p.1.1 p.1.2)) :=
    ((NumberedHeadWindowPrimrecProof.memberPrimitive (HeadCode (Fin n))).comp hg hheads).decide
  have hequivalent : Primrec (fun p : HeadMoveInput n =>
      decide (RecursiveComparison.headEquivalent (decodeHead p.2.1.1) (decodeHead p.2.2.1))) :=
    (NumberedExchangeGuardsPrimrecProof.headEquivalencePrimitive n).comp
      (g := fun p : HeadMoveInput n => (p.2.1.1, p.2.2.1)) (hf.pair hg)
  have hpermutation : Primrec (fun p : HeadMoveInput n => argumentPermutation p.2.1.2 p.2.2.2) :=
    (argumentPermutationPrimitive n).comp hbase htarget
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hwindow hmember) hequivalent) hpermutation

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
