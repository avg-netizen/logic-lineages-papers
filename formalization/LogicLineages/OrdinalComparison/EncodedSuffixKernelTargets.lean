module
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedNatNoteCorrect : Prop :=
  ∀ n : Nat, encodedNatNote n=rawNoteEncode (ONote.ofNat n)

def EncodedKernelBuildersPrimitiveRecursive : Prop :=
  Primrec encodedNatNote ∧
    Primrec (fun p : Nat × Nat × Nat => encodedKernelInitial p.1 p.2.1 p.2.2)

def EncodedKernelInitialCorrect : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ a t : Nat,
    let code := encodedKernelInitial (rawNoteEncode eta.1) a t
    ONote.NF (rawNoteDecode code) ∧
      (rawNoteDecode code).repr=actualSuffixKernelInitial (Ordinal.omega0^eta.1.repr) a t ∧
      actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+rawNormCode (rawNoteEncode eta.1)

def EncodedSuffixKernelCorrect : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ a t : Nat,
    a+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t →
      encodedSuffixKernelCount (rawNoteEncode eta.1) a t=actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) a t ∧
      encodedSuffixKernelValue (rawNoteEncode eta.1) a t=actualSuffixKernel (Ordinal.omega0^eta.1.repr) a t

def EncodedSuffixKernelComputable : Prop :=
  Computable (fun p : Nat × Nat × Nat => encodedSuffixKernelCount p.1 p.2.1 p.2.2) ∧
    Computable (fun p : Nat × Nat × Nat => encodedSuffixKernelValue p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.Targets
