module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalTypedDecoder OriginalTypedDecoderInternalBranchProof
open OriginalRawSyntaxTransport (constant)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exact common subexpression of the frozen lambda/cons/ordinary/numbered
branches: nonzero control, then equality, with literal zero on either failure. -/
def guardProgram {n : Nat} (control left right yes : Program n) : Program n :=
  InternalAcceptance.branch control (constant n 0) (ifSame left right yes (constant n 0))

def guardSpec (out c x y : OTerm alpha) (accepted : Formula alpha) : Formula alpha :=
  ((equal c (numeral 0)).not ⊓ (equal x y ⊓ accepted)) ⊔
    ((equal c (numeral 0) ⊔ (equal x y).not) ⊓ equal out (numeral 0))

 theorem guardForward {n : Nat} (control left right yes : Program n)
    (out c x y : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hl : Nonempty (Derivation body Delta (programGraph left x xs)))
    (hr : Nonempty (Derivation body Delta (programGraph right y xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (guardProgram control left right yes) out xs))) :
    Nonempty (Derivation body Delta (guardSpec out c x y (programGraph yes out xs))) := by
  unfold guardSpec
  apply formulaCases (equal c (numeral 0)) _
  · have hz : Nonempty (Derivation body (equal c (numeral 0) :: Delta) (equal c (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hout := zeroAtElim control (constant n 0) (ifSame left right yes (constant n 0))
      out c xs (withHyp hc _) hz (withHyp ho _)
    have he := constantForward 0 out xs hout
    obtain ⟨hz⟩ := hz
    obtain ⟨he⟩ := he
    exact ⟨orRight (Derivation.conjunctionIntroduction (orLeft hz) he)⟩
  · have hn : Nonempty (Derivation body ((equal c (numeral 0)).not :: Delta)
        (equal c (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply formulaCases (equal x y) _
    · have he : Nonempty (Derivation body
          (equal x y :: (equal c (numeral 0)).not :: Delta) (equal x y)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hbranch := nonzeroAtElim (Delta := equal x y :: (equal c (numeral 0)).not :: Delta) control (constant n 0) (ifSame left right yes (constant n 0))
        out c xs (withHyp (withHyp hc _) _) (withHyp hn _) (withHyp (withHyp ho _) _)
      have hy := sameYesElim left right yes (constant n 0) out x y xs
        (withHyp (withHyp hl _) _) (withHyp (withHyp hr _) _) he hbranch
      obtain ⟨hyes⟩ := andIntro (withHyp hn _) (andIntro he hy)
      exact ⟨orLeft hyes⟩
    · have he : Nonempty (Derivation body
          ((equal x y).not :: (equal c (numeral 0)).not :: Delta) (equal x y).not) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hbranch := nonzeroAtElim (Delta := (equal x y).not :: (equal c (numeral 0)).not :: Delta) control (constant n 0) (ifSame left right yes (constant n 0))
        out c xs (withHyp (withHyp hc _) _) (withHyp hn _) (withHyp (withHyp ho _) _)
      have hz := sameNoElim left right yes (constant n 0) out x y xs
        (withHyp (withHyp hl _) _) (withHyp (withHyp hr _) _) he hbranch
      obtain ⟨he⟩ := he
      obtain ⟨hz⟩ := constantForward 0 out xs hz
      exact ⟨orRight (Derivation.conjunctionIntroduction (orRight he) hz)⟩

/-- Equality rejection works independently of whether the outer control is
zero. This retains both failure paths of the actual nested branch AST. -/
 theorem guardMismatch {n : Nat} (control left right yes : Program n)
    (out c x y : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hl : Nonempty (Derivation body Delta (programGraph left x xs)))
    (hr : Nonempty (Derivation body Delta (programGraph right y xs)))
    (he : Nonempty (Derivation body Delta (equal x y).not))
    (hz : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph (guardProgram control left right yes) out xs)) := by
  apply formulaCases (equal c (numeral 0)) _
  · have hzero : Nonempty (Derivation body (equal c (numeral 0) :: Delta) (equal c (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact zeroAtIntro control (constant n 0) (ifSame left right yes (constant n 0))
      out c xs (withHyp hc _) hzero (constantBackward 0 out xs (withHyp hz _))
  · have hnonzero : Nonempty (Derivation body ((equal c (numeral 0)).not :: Delta)
        (equal c (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply nonzeroAtIntro control (constant n 0) (ifSame left right yes (constant n 0))
      out c xs (withHyp hc _) hnonzero
    exact sameNoIntro left right yes (constant n 0) out x y xs (withHyp hl _) (withHyp hr _)
      (withHyp he _) (constantBackward 0 out xs (withHyp hz _))

 theorem guardBackward {n : Nat} (control left right yes : Program n)
    (out c x y : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hl : Nonempty (Derivation body Delta (programGraph left x xs)))
    (hr : Nonempty (Derivation body Delta (programGraph right y xs)))
    (ho : Nonempty (Derivation body Delta (guardSpec out c x y (programGraph yes out xs)))) :
    Nonempty (Derivation body Delta (programGraph (guardProgram control left right yes) out xs)) := by
  apply orCases ho
  · have hgood : Nonempty (Derivation body
        (((equal c (numeral 0)).not ⊓ (equal x y ⊓ programGraph yes out xs)) :: Delta)
        ((equal c (numeral 0)).not ⊓ (equal x y ⊓ programGraph yes out xs))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply nonzeroAtIntro control (constant n 0) (ifSame left right yes (constant n 0))
      out c xs (withHyp hc _) (andLeft hgood)
    exact sameYesIntro left right yes (constant n 0) out x y xs (withHyp hl _) (withHyp hr _)
      (andLeft (andRight hgood)) (andRight (andRight hgood))
  · have hbad : Nonempty (Derivation body
        (((equal c (numeral 0) ⊔ (equal x y).not) ⊓ equal out (numeral 0)) :: Delta)
        ((equal c (numeral 0) ⊔ (equal x y).not) ⊓ equal out (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases (andLeft hbad)
    · have hzero : Nonempty (Derivation body
          (equal c (numeral 0) :: ((equal c (numeral 0) ⊔ (equal x y).not) ⊓ equal out (numeral 0)) :: Delta)
          (equal c (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact zeroAtIntro control (constant n 0) (ifSame left right yes (constant n 0))
        out c xs (withHyp (withHyp hc _) _) hzero
        (constantBackward 0 out xs (withHyp (andRight hbad) _))
    · have hmismatch : Nonempty (Derivation body
          ((equal x y).not :: ((equal c (numeral 0) ⊔ (equal x y).not) ⊓ equal out (numeral 0)) :: Delta)
          (equal x y).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact guardMismatch control left right yes out c x y xs
        (withHyp (withHyp hc _) _) (withHyp (withHyp hl _) _) (withHyp (withHyp hr _) _)
        hmismatch (withHyp (andRight hbad) _)


/-- Logical transport changes only the accepting branch's formula. Both
literal rejection reasons and every output are retained. -/
 theorem guardSpecMap (out c x y : OTerm alpha) (P Q : Formula alpha)
    (hpq : Nonempty (Derivation body Delta (P.imp Q)))
    (ho : Nonempty (Derivation body Delta (guardSpec out c x y P))) :
    Nonempty (Derivation body Delta (guardSpec out c x y Q)) := by
  apply orCases ho
  · have hs : Nonempty (Derivation body
        (((equal c (numeral 0)).not ⊓ (equal x y ⊓ P)) :: Delta)
        ((equal c (numeral 0)).not ⊓ (equal x y ⊓ P))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hi⟩ := withHyp hpq ((equal c (numeral 0)).not ⊓ (equal x y ⊓ P))
    obtain ⟨hp⟩ := andRight (andRight hs)
    obtain ⟨hq⟩ := andIntro (andLeft hs)
      (andIntro (andLeft (andRight hs)) ⟨Derivation.implicationElimination hi hp⟩)
    exact ⟨orLeft hq⟩
  · exact ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
