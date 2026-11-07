module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathCoreProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPathCertificates NumberedNumericQuotientEdge ApplicationCertificateLiftPath

theorem actualLength : ApplicationCertificateLiftPathTargets.ActualLength := by
  intro n arity Gamma context domain codomain argument entries
  simp [liftEntries]

theorem vertexCalibration (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (hc : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (Gamma : List Ty) (sigma tau : Ty) (context : Nat)
    (hctx : Encodable.decode context = some ctx)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse ctx.1.1 ctx.1.2 f) (ha : InUniverse ctx.1.1 ctx.1.2 a)
    (hcan : representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩ =
      packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)) :
    vertex n arity Gamma context (typeNumber sigma) (typeNumber tau)
      (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma))
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩) =
      representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app f a⟩ := by
  have h := NumberedNumericApplicationProof.canonicalApplicationCalibration n arity
    ctx.1.1 ctx.1.2 hc Gamma sigma tau f a hf ha
  rw [hcan] at h
  simp [vertex,OrdinaryArithmeticApplication.decodedApplication,hctx,
    (NumberedNumericDecodingProof.typeNumericRoundTrip sigma),
    (NumberedNumericDecodingProof.typeNumericRoundTrip tau),h,NumberedQuotientApplication.applicationPacked]

theorem actualPathLift : ApplicationCertificateLiftPathTargets.ActualPathLift := by
  intro n arity ctx hc Gamma sigma tau context hctx f g a entries hf hg ha hcan h
  induction entries generalizing f with
  | nil =>
    have he : representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩ =
        representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩ := by simpa [pathTest] using h
    have he' := NumberedQuotientApplicationProof.representativeApplicationCongruence n arity
      ctx.1.1 ctx.1.2 hc Gamma sigma tau f g a a hf hg ha ha he rfl
    simpa [liftEntries,pathTest,NumberedQuotientApplication.applicationPacked] using he'
  | cons entry entries ih =>
    obtain ⟨z,certificate⟩ := entry
    have hh : numericEdgeTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩) z certificate = true ∧
        pathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 z
          (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩) entries = true := by
      simpa [pathTest] using h
    obtain ⟨q,r,hq,hr,hqn,hrn,hqr,hrr,hs⟩ :=
      ApplicationCertificateLiftEdgeProof.actualTypedEdgePresentation n arity
        ctx.1.1 ctx.1.2 hc Gamma ctx.2 sigma tau f z certificate hf hh.1
    have he : numericEdgeTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩)
        (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,r⟩) certificate = true := by
      simpa only [hrr] using hh.1
    have he' := ApplicationCertificateLiftEdgeProof.actualOriginalEdgeLift n arity
      ctx.1.1 ctx.1.2 hc Gamma ctx.2 sigma tau f r a certificate hf hr ha he
    have hrest := ih r hr (by simpa only [hrr] using hh.2)
    have hv := vertexCalibration n arity ctx hc Gamma sigma tau context hctx r a hr ha hcan
    rw [hrr] at hv
    simpa [liftEntries,pathTest,hv] using And.intro he' hrest

theorem actualPositiveLift : ApplicationCertificateLiftPathTargets.ActualPositiveLift := by
  intro n arity ctx hc Gamma sigma tau context hctx f g a certificate hf hg ha hcan h
  cases hd : decodePathCertificate certificate with
  | none => simp [positivePathTest,hd] at h
  | some entries =>
    cases entries with
    | nil => simp [positivePathTest,hd] at h
    | cons entry entries =>
      have hp : pathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
          (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩)
          (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩) (entry::entries) = true := by
        simpa [positivePathTest,hd] using h
      have hnew := actualPathLift n arity ctx hc Gamma sigma tau context hctx f g a
        (entry::entries) hf hg ha hcan hp
      simpa [liftPath,hd,NumberedQuotientPathCertificatesProof.certificateRoundTrip,
        liftEntries,positivePathTest] using hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathCoreProof
