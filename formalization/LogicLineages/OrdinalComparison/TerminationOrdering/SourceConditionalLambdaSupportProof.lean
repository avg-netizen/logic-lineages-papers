module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaSupportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication SourceComputabilityFormula

theorem applicationComputable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse ctx.1.1 ctx.1.2 f) (ha : InUniverse ctx.1.1 ctx.1.2 a)
    (hcf : Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context (.arrow sigma tau) (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩))
    (hca : Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context sigma (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩)) :
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau (representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a)) := by
  obtain ⟨z,hz,hcz⟩ := hcf.2 _ hca
  rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc sigma tau,
    NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau f a hf ha] at hz
  cases Option.some.inj hz
  exact hcz

theorem betaPrimaryCode (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (hc : SubtypeClosed (fun t => t ∈ S)) (Gamma : List Ty) (sigma tau : Ty)
    (body body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (a : AuxTerm (Fin n) arity Gamma sigma)
    (hb : InUniverse symbols S body) (hb' : InUniverse symbols S body') (ha : InUniverse symbols S a)
    (hp : NumberedWindowEquivalence.WindowPrimary (Fin n) arity symbols S (sigma :: Gamma) ⟨tau,body⟩ ⟨tau,body'⟩) :
    representativeCode symbols S (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) =
    representativeCode symbols S (⟨tau,substitute body' (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) := by
  have h1 := NumberedUniverseBindingProof.actualBeta (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma sigma tau body a hb ha
  have h2 := NumberedUniverseBindingProof.actualBeta (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma sigma tau body' a hb' ha
  exact (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma ⟨tau,substitute body (singleSubstitution a)⟩ ⟨tau,substitute body' (singleSubstitution a)⟩ h1 h2).mpr
    (NumberedPrimarySubstitutionProof.actualPrimarySubstitution (Fin n) arity symbols S (sigma :: Gamma) Gamma
      (singleSubstitution a) ⟨tau,body⟩ ⟨tau,body'⟩ hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaSupportProof
