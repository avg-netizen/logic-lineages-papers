module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalClassProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedFinitePrimaryClass OriginalLambdaCanonical OriginalLambdaCanonicalTargets

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem bodyConfinement {Symbol : Type} {arity : Symbol → Nat}
    {symbols : List Symbol} {S Gamma : List Ty} {sigma tau : Ty}
    {body : AuxTerm Symbol arity (sigma :: Gamma) tau}
    (h : InUniverse symbols S (AuxTerm.lam body)) : InUniverse symbols S body :=
  ⟨h.1.2.2,h.2⟩

theorem replacedLambdaConfinement {Symbol : Type} {arity : Symbol → Nat}
    {symbols : List Symbol} {S Gamma : List Ty} {sigma tau : Ty}
    {body body' : AuxTerm Symbol arity (sigma :: Gamma) tau}
    (h : InUniverse symbols S (AuxTerm.lam body)) (h' : InUniverse symbols S body') :
    InUniverse symbols S (AuxTerm.lam body') :=
  ⟨⟨h.1.1,h.1.2.1,h'.1⟩,h'.2⟩

theorem actualOriginalLambdaPrimaryClassImage : ActualOriginalLambdaPrimaryClassImage := by
  intro n arity symbols S hc Gamma sigma tau body hlambda q
  have hbody := bodyConfinement hlambda
  constructor
  · intro hq
    have hp := (NumberedFinitePrimaryClassProof.exactPrimaryClass
      (Fin n) inferInstance arity symbols S hc Gamma (lambdaPacked body) hlambda q).mp hq
    obtain ⟨body',he,hp⟩ := (NumberedPrimaryLambdaBodyProof.actualPrimaryLambdaBody
      (Fin n) arity symbols S Gamma sigma tau body q).mp hp
    exact ⟨body',he,(NumberedFinitePrimaryClassProof.exactPrimaryClass
      (Fin n) inferInstance arity symbols S hc (sigma :: Gamma) ⟨tau,body⟩ hbody
        ⟨tau,body'⟩).mpr hp⟩
  · rintro ⟨body',rfl,hbody'⟩
    apply (NumberedFinitePrimaryClassProof.exactPrimaryClass
      (Fin n) inferInstance arity symbols S hc Gamma (lambdaPacked body) hlambda
        (lambdaPacked body')).mpr
    exact .lam body body' ((NumberedFinitePrimaryClassProof.exactPrimaryClass
      (Fin n) inferInstance arity symbols S hc (sigma :: Gamma) ⟨tau,body⟩ hbody
        ⟨tau,body'⟩).mp hbody')

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalClassProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalClassProof
