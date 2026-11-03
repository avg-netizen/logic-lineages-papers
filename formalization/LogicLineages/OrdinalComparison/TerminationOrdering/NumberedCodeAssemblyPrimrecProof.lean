module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedCodeView
open NumberedHeadCodecPrimrecSupportProof

theorem varPrimitive (n : Nat) : Primrec (@Code.var (Fin n)) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun index : Nat => Nat.pair 0 index)
  exact Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem lamPrimitive (n : Nat) :
    Primrec (fun p : Ty × Code (Fin n) => Code.lam p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Ty × Code (Fin n) =>
    Nat.pair 1 (Nat.pair (typeNumber p.1) (codeNumber p.2)))
  exact Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
      ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd))

theorem appPrimitive (n : Nat) :
    Primrec (fun p : Ty × Code (Fin n) × Code (Fin n) => Code.app p.1 p.2.1 p.2.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Ty × Code (Fin n) × Code (Fin n) =>
    Nat.pair 2 (Nat.pair (typeNumber p.1) (Nat.pair (codeNumber p.2.1) (codeNumber p.2.2))))
  exact Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
      (Primrec₂.natPair.comp
        ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.fst.comp Primrec.snd))
        ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.snd.comp Primrec.snd))))

theorem bottomPrimitive (n : Nat) : Primrec (@Code.bottom (Fin n)) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun tau : Ty => Nat.pair 3 (typeNumber tau))
  exact Primrec₂.natPair.comp (Primrec.const 3) NumberedTypeCodecPrimrecProof.typeEncoderPrimitive

theorem ordinaryPrimitive (n : Nat) :
    Primrec (fun p : HeadCode (Fin n) × Code (Fin n) => Code.ordinary p.1 p.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : HeadCode (Fin n) × Code (Fin n) =>
    Nat.pair 4 (Nat.pair (headNumber p.1) (codeNumber p.2)))
  exact Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp
      ((NumberedHeadCodecPrimrecProof.headEncoderPrimitive n).comp Primrec.fst)
      ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd))

abbrev NumberedData (n : Nat) :=
  Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n)

theorem numberedPrimitive (n : Nat) :
    Primrec (fun p : NumberedData n =>
      Code.numbered p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : NumberedData n => Nat.pair 5
    (Nat.pair p.1 (Nat.pair (headNumber p.2.1) (Nat.pair (typeNumber p.2.2.1)
      (Nat.pair (codeNumber p.2.2.2.1) (Nat.pair (typesNumber p.2.2.2.2.1)
        (codeNumber p.2.2.2.2.2)))))))
  have ht2 : Primrec (fun p : NumberedData n => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht3 : Primrec (fun p : NumberedData n => p.2.2.2) := Primrec.snd.comp ht2
  have ht4 : Primrec (fun p : NumberedData n => p.2.2.2.2) := Primrec.snd.comp ht3
  exact Primrec₂.natPair.comp (Primrec.const 5)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp
        ((NumberedHeadCodecPrimrecProof.headEncoderPrimitive n).comp (Primrec.fst.comp Primrec.snd))
        (Primrec₂.natPair.comp
          (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp (Primrec.fst.comp ht2))
          (Primrec₂.natPair.comp
            ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.fst.comp ht3))
            (Primrec₂.natPair.comp
              (NumberedTypeCodecPrimrecProof.typeListEncoderPrimitive.comp (Primrec.fst.comp ht4))
              ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.snd.comp ht4)))))))

theorem argumentsConsPrimitive (n : Nat) :
    Primrec (fun p : Ty × Code (Fin n) × Code (Fin n) => Code.argumentsCons p.1 p.2.1 p.2.2) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun p : Ty × Code (Fin n) × Code (Fin n) =>
    Nat.pair 7 (Nat.pair (typeNumber p.1) (Nat.pair (codeNumber p.2.1) (codeNumber p.2.2))))
  exact Primrec₂.natPair.comp (Primrec.const 7)
    (Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
      (Primrec₂.natPair.comp
        ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.fst.comp Primrec.snd))
        ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp (Primrec.snd.comp Primrec.snd))))

theorem unviewPrimitive : NumberedCodeAssemblyPrimrecTargets.ActualUnviewPrimitive := by
  intro n
  have h : Primrec (fun data : CodeView n => data.elim (@Code.var (Fin n))
      (Sum.elim (fun p => Code.lam p.1 p.2)
        (Sum.elim (fun p => Code.app p.1 p.2.1 p.2.2)
          (Sum.elim Code.bottom
            (Sum.elim (fun p => Code.ordinary p.1 p.2)
              (Sum.elim (fun p => Code.numbered p.1 p.2.1 p.2.2.1 p.2.2.2.1
                  p.2.2.2.2.1 p.2.2.2.2.2)
                (Sum.elim (fun _ => Code.argumentsNil)
                  (fun p => Code.argumentsCons p.1 p.2.1 p.2.2)))))))) :=
    sumElim (varPrimitive n) (sumElim (lamPrimitive n) (sumElim (appPrimitive n)
      (sumElim (bottomPrimitive n) (sumElim (ordinaryPrimitive n)
        (sumElim (numberedPrimitive n) (sumElim (Primrec.const Code.argumentsNil)
          (argumentsConsPrimitive n)))))))
  apply h.of_eq
  intro data
  rcases data with index | ⟨sigma, body⟩ | ⟨sigma, q, a⟩ | tau |
    ⟨head, base⟩ | ⟨k, head, tau, base, types, extras⟩ | unit | ⟨tau, q, rest⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases unit
    rfl
  · rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof
