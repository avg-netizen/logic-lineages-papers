module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedAuxiliaryCoding NumberedStepContexts NumberedTypedFocus NumberedNumericDecoding
open NumberedNumericRoot NumberedNumericCarrier NumberedStepCertificate NumberedNumericStep
open ApplicationCertificateLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualTypedLift : ApplicationCertificateLiftTargets.ActualTypedLift := by
  intro n arity symbols S Gamma table sigma tau q r a c
  cases hf : focus c.path q with
  | none => simp [stepTest,liftCertificate,focus,hf]
  | some f =>
    cases hb : decodePackedNumber n arity f.holeGamma c.replacement with
    | none => simp [stepTest,liftCertificate,focus,hf,hb]
    | some b =>
      obtain ⟨beta,b⟩ := b
      cases hs : decodeSelector n arity f.holeGamma c.root with
      | none => simp [stepTest,liftCertificate,focus,hf,hb,hs]
      | some selector =>
        simp only [stepTest,liftCertificate,focus,hf,Option.map_some,hb,hs]
        split
        next ht =>
          cases ht
          simp [plug,packedNumber,termCode,codeNumber]
        next _ => simp

theorem actualApplicationEncoding : ApplicationCertificateLiftTargets.ActualApplicationEncoding := by
  intro n arity Gamma sigma tau q a
  simp [rawApplication,packedNumber,termCode,codeNumber]

theorem actualStepEncoding : ApplicationCertificateLiftTargets.ActualStepEncoding := by
  intro c
  simp [liftStep,stepCertificateNumber,liftCertificate,pathNumber,
    NumberedMultisetNumeric.numbersNumber]

attribute [local irreducible] Primrec

theorem actualPrimitive : ApplicationCertificateLiftTargets.ActualPrimitive := by
  have getP (i : Fin 4) : Primrec (fun v : List.Vector Nat 4 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have happ : Primrec applicationValue :=
    Primrec₂.natPair.comp (getP 1) (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (getP 0) (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (getP 2)))
        (Primrec.snd.comp (Primrec.unpair.comp (getP 3))))))
  have hs : Primrec liftStep :=
    Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp
        (Primrec.const (positionNumber .appFunction)) (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair)
  exact ⟨happ,hs,hs.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))⟩

theorem actualProgramWitnesses : ApplicationCertificateLiftTargets.ActualProgramWitnesses := by
  obtain ⟨application,ha⟩ := Proof.allPrimitiveFunctions 4 applicationValue actualPrimitive.1
  obtain ⟨step,hs⟩ := Proof.allPrimitiveFunctions 1 stepValue actualPrimitive.2.2
  exact ⟨application,step,ha,hs⟩

theorem actualOriginalNumericLift : ApplicationCertificateLiftTargets.ActualOriginalNumericLift := by
  intro n arity symbols S hc Gamma table sigma tau q r a certificate hq ha h
  have hdq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
    ⟨.arrow sigma tau,q⟩).mpr ⟨rfl,hq⟩
  have hdr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
    (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)
  cases hd : decodeStepCertificate certificate with
  | none => simp [numericStepTest,hdq,hdr,hd] at h
  | some c =>
    have ht : stepTest n arity symbols S Gamma table q r c = true := by
      simpa [numericStepTest,hdq,hdr,hd] using h
    have he := NumberedNumericStepProof.stepCertificateNumericSound certificate c hd
    have hl : decodeStepCertificate (liftStep certificate) = some (liftCertificate c) := by
      rw [← he,actualStepEncoding]
      exact NumberedNumericStepProof.stepCertificateNumericRoundTrip (liftCertificate c)
    have hqa := NumberedQuotientApplicationProof.applicationConfinement
      (Fin n) arity symbols S hc Gamma sigma tau q a hq ha
    have hdaq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
      ⟨tau,.app q a⟩).mpr ⟨rfl,hqa⟩
    have hdar := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
      (⟨tau,.app r a⟩ : Packed (Fin n) arity Gamma)
    rw [actualApplicationEncoding,actualApplicationEncoding]
    have htest := (actualTypedLift n arity symbols S Gamma table sigma tau q r a c).trans ht
    simpa [numericStepTest,hdaq,hdar,hl] using htest

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
