module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
  NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
  NumberedNumericDecoding NumberedNumericCarrier NumberedFiniteUniverse
  NumberedCopyCertificate NumberedSelfApplication NumberedCopyOperation

attribute [local irreducible] Primrec

theorem headAbovePrimitive : NumberedCopyOperationTargets.ActualHeadAbovePrimitive :=
  NumberedCopyOperationSupportProof.headAbovePrimitive

theorem allCopyCodePrimitive : NumberedCopyOperationTargets.ActualAllCopyCodePrimitive :=
  NumberedCopyOperationSupportProof.allCopyCodePrimitive

theorem copyCodeCalibration : NumberedCopyOperationTargets.ActualCopyCodeCalibration := by
  intro n arity Gamma symbols S table g q
  rcases q with ⟨tau, q⟩
  cases q with
  | var v => rfl
  | lam body => rfl
  | app f a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | numbered k f tau base types extras =>
    cases k with
    | zero => rfl
    | succ k =>
      have hself := (NumberedSelfApplicationSupportProof.typedSelfArgumentsCalibration
        (Fin n) arity Gamma k f base types extras (headArguments arity (decodeHead g))).1
      by_cases hg : tau = headResult (decodeHead g) ∧
          RecursiveComparison.headAbove (tableAbove table) f (decodeHead g) ∧
          HeadInWindow arity symbols S (decodeHead g)
      · simp [termCode, copyCode, copyTarget, NumberedAuxiliaryDecodingProof.headRoundTrip,
          NumberedAuxiliaryDecodingProof.headSound, hg, hself]
      · simp [termCode, copyCode, copyTarget, NumberedAuxiliaryDecodingProof.headRoundTrip, hg]

attribute [local irreducible] copyTarget

theorem copyTypePreservation {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (table : Table n) (g : Head (Fin n))
    (q r : Packed (Fin n) arity Gamma)
    (h : copyTarget arity symbols S table Gamma g q = some r) : r.1 = q.1 := by
  have hi := (NumberedCopyCertificateProof.typedCopyCheck n arity symbols S table Gamma g q r).mp h
  cases hi
  rfl

theorem packedCopyPrimitive : NumberedCopyOperationTargets.ActualPackedCopyPrimitive := by
  intro n arity Gamma
  let Input := (List (Fin n) × List Ty) ×
    (Table n × HeadCode (Fin n)) × Packed (Fin n) arity Gamma
  have hs : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have hinput : Primrec (fun p : Input => (p.1, p.2.1, termCode p.2.2.2)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp
        ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp hs)))
  have hr : Primrec (fun p : Input =>
      copyCode arity p.1.1 p.1.2 p.2.1.1 p.2.1.2 (termCode p.2.2.2)) :=
    (allCopyCodePrimitive n arity).comp hinput
  exact NumberedDirectOperationsProof.reconstructSameType
    (fun p : Input => p.2.2)
    (fun p => copyTarget arity p.1.1 p.1.2 p.2.1.1 Gamma (decodeHead p.2.1.2) p.2.2)
    (fun p => copyCode arity p.1.1 p.1.2 p.2.1.1 p.2.1.2 (termCode p.2.2.2))
    hs hr
    (fun p => copyCodeCalibration n arity Gamma p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)
    (fun p r h => copyTypePreservation p.1.1 p.1.2 p.2.1.1 (decodeHead p.2.1.2) p.2.2 r h)

abbrev NumericInput (n : Nat) :=
  (List (Fin n) × List Ty) × Table n × Nat × Nat × Nat

theorem numericCopyCertificatePrimitive :
    NumberedCopyOperationTargets.ActualNumericCopyCertificatePrimitive := by
  intro n arity Gamma
  let P := Packed (Fin n) arity Gamma
  let B := NumericInput n × P
  let C := B × HeadCode (Fin n)
  have hsource : Primrec (fun p : NumericInput n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have htarget : Primrec (fun p : NumericInput n => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hcertificate : Primrec (fun p : NumericInput n => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdata : Primrec (fun p : C => p.1.1) := Primrec.fst.comp Primrec.fst
  have hcopyTarget : Primrec (fun p : C =>
      copyTarget arity p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 Gamma (decodeHead p.2) p.1.2) :=
    (packedCopyPrimitive n arity Gamma).comp
      ((Primrec.fst.comp hdata).pair
        (((Primrec.fst.comp (Primrec.snd.comp hdata)).pair Primrec.snd).pair
          (Primrec.snd.comp Primrec.fst)))
  have hmatch : Primrec (fun p : C × P =>
      decide (packedNumber p.2 = p.1.1.1.2.2.2.1)) :=
    (Primrec.eq.comp
      ((NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma).comp Primrec.snd)
      (htarget.comp (hdata.comp Primrec.fst))).decide
  have hcopy : Primrec (fun p : C =>
      (Option.casesOn
        (copyTarget arity p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 Gamma (decodeHead p.2) p.1.2)
        false (fun r => decide (packedNumber r = p.1.1.2.2.2.1)) : Bool)) :=
    Primrec.option_casesOn hcopyTarget (Primrec.const false) hmatch.to₂
  have hhead : Primrec (fun p : B =>
      (Option.casesOn (decodeHeadNumber n p.1.2.2.2.2) false (fun g =>
        Option.casesOn
          (copyTarget arity p.1.1.1 p.1.1.2 p.1.2.1 Gamma (decodeHead g) p.2)
          false (fun r => decide (packedNumber r = p.1.2.2.2.1))) : Bool)) :=
    Primrec.option_casesOn
      ((NumberedHeadCodecPrimrecProof.headDecoderPrimitive n).comp
        (hcertificate.comp Primrec.fst)) (Primrec.const false) hcopy.to₂
  have hprogram : Primrec (fun p : NumericInput n =>
      (Option.casesOn (decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.2.1) false (fun q =>
        Option.casesOn (decodeHeadNumber n p.2.2.2.2) false (fun g =>
          Option.casesOn (copyTarget arity p.1.1 p.1.2 p.2.1 Gamma (decodeHead g) q)
            false (fun r => decide (packedNumber r = p.2.2.2.1)))) : Bool)) :=
    Primrec.option_casesOn
      ((NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
        (Primrec.fst.pair hsource)) (Primrec.const false) hhead.to₂
  apply hprogram.of_eq
  intro p
  cases hs : decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.2.1 with
  | none => simp [copyCertificateTest, hs]
  | some q =>
    cases hg : decodeHeadNumber n p.2.2.2.2 with
    | none => simp [copyCertificateTest, hs, hg]
    | some g =>
      cases hr : copyTarget arity p.1.1 p.1.2 p.2.1 Gamma (decodeHead g) q with
      | none => simp [copyCertificateTest, hs, hg, hr]
      | some r => simp [copyCertificateTest, hs, hg, hr]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationProof
