module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityMembersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceConstructorComputability SourceConstructorComputabilityMembersProof

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

theorem selfArgumentsComputable (k : Nat) (f : Head (Fin n))
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments (Fin n) arity Gamma extraTypes)
    (types : List Ty)
    (h : ∀ tau ∈ types, TermC context ctx scalar (.numbered k f tau base extraTypes extras)) :
    ArgumentsC context ctx scalar (selfArguments k f base extraTypes extras types) := by
  induction types with
  | nil => intro p hp; cases hp
  | cons tau types ih =>
    exact argumentsCCons (h tau (by simp)) (ih (fun upsilon hu => h upsilon (by simp [hu])))

theorem completeApplicationComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (types : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma (arrows types tau))
    (args : AuxArguments (Fin n) arity Gamma types)
    (hgq : InUniverse ctx.1.1 ctx.1.2 q)
    (hga : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) args)
    (hcq : TermC context ctx scalar q) (hca : ArgumentsC context ctx scalar args) :
    TermC context ctx scalar (applyArguments q args) := by
  induction types with
  | nil => cases args; exact hcq
  | cons sigma types ih =>
    cases args with
    | cons a rest =>
      have ha : InUniverse ctx.1.1 ctx.1.2 a := ⟨hga.1.1,hga.2.1⟩
      have hr : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
          (HeadInWindow arity ctx.1.1 ctx.1.2) rest := ⟨hga.1.2,hga.2.2⟩
      have hcf := SourceConditionalLambdaSupportProof.applicationComputable n arity Gamma context ctx scalar
        hc hclosed sigma (arrows types tau) q a hgq ha hcq
        ((argumentsC_iff (.cons a rest)).mp hca ⟨sigma,a⟩ (by simp [argumentList]))
      have ht := NumberedUniverseOperationsProof.arrowCodomain (fun t => t ∈ ctx.1.2)
        hclosed sigma (arrows types tau)
        (NumberedUniverseOperationsProof.rootType _ _ q hgq)
      have hgf : InUniverse ctx.1.1 ctx.1.2 (.app q a) :=
        ⟨⟨ht,hgq.1,ha.1⟩,hgq.2,ha.2⟩
      exact ih (.app q a) rest hgf hr hcf (fun p hp => hca p (List.mem_cons_of_mem _ hp))

theorem openedComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (k : Nat) (f : Head (Fin n)) (sigma tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
    (hg : InUniverse ctx.1.1 ctx.1.2 (.lam (openNumbered k f sigma tau base types extras)))
    (he : ArgumentsC context ctx scalar extras)
    (hlower : ∀ (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types' extras') →
      ArgumentsC context ctx scalar extras' → TermC context ctx scalar (.numbered k f tau base types' extras')) :
    TermC context ctx scalar (.lam (openNumbered k f sigma tau base types extras)) := by
  apply SourceLambdaComputabilityProof.actualLambdaComputability n arity Gamma context ctx scalar
    hc hclosed hcal sigma tau _ hg
  intro a ha hca
  have hb : InUniverse ctx.1.1 ctx.1.2 (openNumbered k f sigma tau base types extras) := ⟨hg.1.2.2,hg.2⟩
  have hsubst := NumberedUniverseBindingProof.actualBeta (Fin n) arity
    (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma sigma tau _ a hb ha
  rw [NumberedRewriteApplicationBindingProof.openedBetaBody] at hsubst ⊢
  exact hlower _ _ hsubst (argumentsCAppend he (argumentsCCons hca (by intro p hp; cases hp)))
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityApplicationProof
