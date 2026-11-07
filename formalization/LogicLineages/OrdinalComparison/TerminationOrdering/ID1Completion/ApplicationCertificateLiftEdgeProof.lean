module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedNumericStep NumberedNumericQuotientEdge NumberedNumericCarrier NumberedNumericDecoding
open ApplicationCertificateLift ApplicationCertificateLiftEdge
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualEncoding : ApplicationCertificateLiftEdgeTargets.ActualEncoding := by
  intro domain codomain argument source target step
  simp [liftEdge,edgeCertificateNumber,sourceOf,targetOf,stepOf]

attribute [local irreducible] Primrec

theorem applicationPrimitive {A : Type} [Primcodable A] {d e f a : A → Nat}
    (hd : Primrec d) (he : Primrec e) (hf : Primrec f) (ha : Primrec a) :
    Primrec (fun z => rawApplication (d z) (e z) (f z) (a z)) :=
  Primrec₂.natPair.comp he (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp hd (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp hf))
      (Primrec.snd.comp (Primrec.unpair.comp ha)))))

theorem actualPrimitive : ApplicationCertificateLiftEdgeTargets.ActualPrimitive := by
  have getP (i : Fin 4) : Primrec (fun v : List.Vector Nat 4 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hq : Primrec (fun v : List.Vector Nat 4 => sourceOf (v.get 3)) :=
    Primrec.fst.comp (Primrec.unpair.comp (getP 3))
  have htail : Primrec (fun v : List.Vector Nat 4 => Nat.unpair (Nat.unpair (v.get 3)).2) :=
    Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 3)))
  have hr : Primrec (fun v : List.Vector Nat 4 => targetOf (v.get 3)) := Primrec.fst.comp htail
  have hs : Primrec (fun v : List.Vector Nat 4 => stepOf (v.get 3)) := Primrec.snd.comp htail
  have hfirst : Primrec (fun v : List.Vector Nat 4 =>
      rawApplication (v.get 0) (v.get 1) (sourceOf (v.get 3)) (v.get 2)) :=
    applicationPrimitive (getP 0) (getP 1) hq (getP 2)
  have hsecond : Primrec (fun v : List.Vector Nat 4 =>
      rawApplication (v.get 0) (v.get 1) (targetOf (v.get 3)) (v.get 2)) :=
    applicationPrimitive (getP 0) (getP 1) hr (getP 2)
  have hlast : Primrec (fun v : List.Vector Nat 4 => liftStep (stepOf (v.get 3))) :=
    ApplicationCertificateLiftProof.actualPrimitive.2.1.comp hs
  have hout := Primrec₂.natPair.comp hfirst (Primrec₂.natPair.comp hsecond hlast)
  exact hout.of_eq (by intro v; rfl)

theorem actualProgramWitness : ApplicationCertificateLiftEdgeTargets.ActualProgramWitness :=
  Proof.allPrimitiveFunctions 4 edgeValue actualPrimitive

theorem actualTypedEdgePresentation : ApplicationCertificateLiftEdgeTargets.ActualTypedEdgePresentation := by
  intro n arity symbols S hc Gamma table sigma tau f y certificate hf h
  have hbody : (match decodeUniverse n arity symbols S Gamma (sourceOf certificate),
      decodePackedNumber n arity Gamma (targetOf certificate) with
    | some q,some r => numericStepTest n arity symbols S Gamma table
        (sourceOf certificate) (targetOf certificate) (stepOf certificate) &&
        decide (representativeCode symbols S q = representativeCode symbols S ⟨.arrow sigma tau,f⟩ ∧
          representativeCode symbols S r = y)
    | _,_ => false) = true := h
  cases hq0 : decodeUniverse n arity symbols S Gamma (sourceOf certificate) with
  | none => simp [hq0] at hbody
  | some q0 =>
    cases hr0 : decodePackedNumber n arity Gamma (targetOf certificate) with
    | none => simp [hq0,hr0] at hbody
    | some r0 =>
      have hh : numericStepTest n arity symbols S Gamma table
          (sourceOf certificate) (targetOf certificate) (stepOf certificate) = true ∧
          representativeCode symbols S q0 = representativeCode symbols S ⟨.arrow sigma tau,f⟩ ∧
          representativeCode symbols S r0 = y := by simpa [hq0,hr0] using hbody
      obtain ⟨beta,q,r,hq,hr,hstep,hqn,hrn⟩ := NumberedNumericStepProof.numericStepSound
        n arity symbols S hc Gamma table (sourceOf certificate) (targetOf certificate) (stepOf certificate) hh.1
      have hq0n := ((NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
        (sourceOf certificate) q0).mp hq0).1
      have hr0n := NumberedNumericDecodingProof.packedNumericSound n arity Gamma
        (targetOf certificate) r0 hr0
      have heq : (⟨beta,q⟩ : Packed (Fin n) arity Gamma) = q0 :=
        NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma (hqn.trans hq0n.symm)
      have her : (⟨beta,r⟩ : Packed (Fin n) arity Gamma) = r0 :=
        NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma (hrn.trans hr0n.symm)
      have hqr : representativeCode symbols S ⟨beta,q⟩ =
          representativeCode symbols S ⟨.arrow sigma tau,f⟩ := by rw [heq]; exact hh.2.1
      have hrr : representativeCode symbols S ⟨beta,r⟩ = y := by rw [her]; exact hh.2.2
      have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
        ⟨beta,q⟩ ⟨.arrow sigma tau,f⟩ hq hf).mp hqr
      have ht : beta = .arrow sigma tau := NumberedPrimaryEquivalenceProof.primaryTypePreservation
        (Fin n) arity Gamma ⟨beta,q⟩ ⟨.arrow sigma tau,f⟩
        (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ hp)
      subst beta
      exact ⟨q,r,hq,hr,hqn,hrn,hqr,hrr,hh.1⟩

theorem actualOriginalEdgeLift : ApplicationCertificateLiftEdgeTargets.ActualOriginalEdgeLift := by
  intro n arity symbols S hc Gamma table sigma tau f g a certificate hf hg ha h
  obtain ⟨q,r,hq,hr,hqn,hrn,hqr,hrr,hs⟩ := actualTypedEdgePresentation
    n arity symbols S hc Gamma table sigma tau f
    (representativeCode symbols S ⟨.arrow sigma tau,g⟩) certificate hf h
  have hs0 : numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)) (stepOf certificate) = true := by
    simpa only [hqn,hrn] using hs
  have hsa := ApplicationCertificateLiftProof.actualOriginalNumericLift n arity symbols S hc Gamma
    table sigma tau q r a (stepOf certificate) hq ha hs0
  rw [ApplicationCertificateLiftProof.actualApplicationEncoding,
    ApplicationCertificateLiftProof.actualApplicationEncoding] at hsa
  have hqa := NumberedQuotientApplicationProof.applicationConfinement
    (Fin n) arity symbols S hc Gamma sigma tau q a hq ha
  have hdq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma)) ⟨tau,.app q a⟩).mpr ⟨rfl,hqa⟩
  have hdr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
    (⟨tau,.app r a⟩ : Packed (Fin n) arity Gamma)
  have heq := NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc
    Gamma sigma tau q f a a hq hf ha ha hqr rfl
  have her := NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc
    Gamma sigma tau r g a a hr hg ha ha hrr rfl
  change representativeCode symbols S ⟨tau,.app q a⟩ = representativeCode symbols S ⟨tau,.app f a⟩ at heq
  change representativeCode symbols S ⟨tau,.app r a⟩ = representativeCode symbols S ⟨tau,.app g a⟩ at her
  unfold liftEdge
  rw [← hqn,← hrn,ApplicationCertificateLiftProof.actualApplicationEncoding,
    ApplicationCertificateLiftProof.actualApplicationEncoding]
  simp [numericEdgeTest,edgeCertificateNumber,hdq,hdr,hsa,heq,her]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeProof
