module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedAuxiliaryCoding NumberedFinitePrimaryClass NumberedLeastCodeRepresentative
open OriginalLambdaCanonical OriginalLambdaCanonicalClassProof

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem lambdaNumberMono {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} {body body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau}
    (h : packedNumber ⟨tau,body⟩ ≤ packedNumber ⟨tau,body'⟩) :
    packedNumber (lambdaPacked body) ≤ packedNumber (lambdaPacked body') := by
  exact NumberedApplicationFactorizationSupportProof.pairMonoRight
    (typeNumber (.arrow sigma tau))
    (NumberedApplicationFactorizationSupportProof.pairMonoRight 1
      (NumberedApplicationFactorizationSupportProof.pairMonoRight (typeNumber sigma)
        (NumberedApplicationFactorizationSupportProof.packedPayloadOrder h)))

theorem canonicalBodyLambdaFixed (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun rho => rho ∈ S))
    (Gamma : List Ty) (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hlambda : InUniverse symbols S (AuxTerm.lam body))
    (hfixed : representativeCode symbols S ⟨tau,body⟩ = packedNumber ⟨tau,body⟩) :
    representativeCode symbols S (lambdaPacked body) = packedNumber (lambdaPacked body) := by
  apply Nat.le_antisymm
  · exact NumberedLeastCodeRepresentativeProof.representativeMinimal
      n arity symbols S hc Gamma (lambdaPacked body) (lambdaPacked body) hlambda (.refl _)
  · obtain ⟨q,hq,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
      n arity symbols S hc Gamma (lambdaPacked body) hlambda
    obtain ⟨body',rfl,hbody'⟩ := (NumberedPrimaryLambdaBodyProof.actualPrimaryLambdaBody
      (Fin n) arity symbols S Gamma sigma tau body q).mp hq
    have hle := NumberedLeastCodeRepresentativeProof.representativeMinimal
      n arity symbols S hc (sigma :: Gamma) ⟨tau,body⟩ ⟨tau,body'⟩
        (bodyConfinement hlambda) hbody'
    rw [hfixed] at hle
    rw [he]
    exact lambdaNumberMono hle

/-- Select the original typed body minimizer and reconstruct the original
lambda minimizer from it. All witnesses come from existing native finite
classes; this does not assert anything about the internal canonical fold. -/
theorem typedLambdaRepresentative (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun rho => rho ∈ S))
    (Gamma : List Ty) (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hlambda : InUniverse symbols S (AuxTerm.lam body)) :
    ∃ body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
      InUniverse symbols S body' ∧
      (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) ∈
        primaryClass symbols S ⟨tau,body⟩ ∧
      representativeCode symbols S ⟨tau,body⟩ = packedNumber ⟨tau,body'⟩ ∧
      representativeCode symbols S ⟨tau,body'⟩ = packedNumber ⟨tau,body'⟩ ∧
      representativeCode symbols S (lambdaPacked body) = packedNumber (lambdaPacked body') := by
  have hbody := bodyConfinement hlambda
  obtain ⟨body',hbody',hp,he,hfixed⟩ :=
    NumberedApplicationFactorizationSupportProof.typedRepresentative
      n arity symbols S hc (sigma :: Gamma) tau body hbody
  have hlambda' := replacedLambdaConfinement hlambda hbody'
  have hrep := (NumberedLeastCodeRepresentativeProof.representativeEquality
    n arity symbols S hc Gamma (lambdaPacked body) (lambdaPacked body')
      hlambda hlambda').mpr (.lam body body' hp)
  exact ⟨body',hbody',(NumberedFinitePrimaryClassProof.exactPrimaryClass
    (Fin n) inferInstance arity symbols S hc (sigma :: Gamma) ⟨tau,body⟩ hbody
      ⟨tau,body'⟩).mpr hp,he,hfixed,hrep.trans
        (canonicalBodyLambdaFixed n arity symbols S hc Gamma sigma tau body' hlambda' hfixed)⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalSupportProof
