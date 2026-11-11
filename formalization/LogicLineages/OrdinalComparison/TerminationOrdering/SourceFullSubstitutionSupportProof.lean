module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionSupportProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient PositiveArithmeticOperators PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceFullSubstitution SourceLambdaEnvironment

theorem liftIdentity {Symbol : Type} {arity : Symbol → Nat} (Gamma : List Ty) (sigma : Ty) :
    (fun {tau : Ty} (v : Variable (sigma :: Gamma) tau) =>
      liftSubstitution (fun w => AuxTerm.var (arity := arity) w) v) =
    (fun {tau : Ty} (v : Variable (sigma :: Gamma) tau) => AuxTerm.var (arity := arity) v) := by
  funext tau v
  cases v <;> rfl

theorem substituteIdentity {Symbol : Type} {arity : Symbol → Nat}
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    substitute q (fun v => AuxTerm.var v) = q := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => substituteArguments args (fun v => AuxTerm.var v) = args)
  case var => rfl
  case lam body ih =>
    simp only [substitute]
    rw [liftIdentity]
    exact congrArg AuxTerm.lam ih
  case app f a ihf iha => exact congrArg₂ AuxTerm.app ihf iha
  case bottom => rfl
  case ordinary f base ih => exact congrArg (AuxTerm.ordinary f) ih
  case numbered k f tau base types extras ihb ihe =>
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e) ihb ihe
  case nil => rfl
  case cons q rest ihq ihr => exact congrArg₂ AuxArguments.cons ihq ihr

theorem extendWindowEnvironment {n : Nat} {arity : Fin n → Nat} {Gamma Delta : List Ty}
    {context : Nat} {ctx : Context n} {scalar : Positive (Fin 2)} {sigma : Ty}
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
    (a : AuxTerm (Fin n) arity Delta sigma)
    (hg : NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) theta)
    (ha : InUniverse ctx.1.1 ctx.1.2 a)
    (he : WindowComputableEnvironment n arity Gamma Delta context ctx scalar theta)
    (hca : Computable n arity Delta (fun x => x ∈ leastSet scalar context) context sigma
      (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩)) :
    NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) (extend theta a) ∧
    WindowComputableEnvironment n arity (sigma :: Gamma) Delta context ctx scalar (extend theta a) := by
  constructor
  · intro tau v ht
    cases v with
    | here => exact ha
    | there v => exact hg v ht
  · intro tau v ht
    cases v with
    | here => exact hca
    | there v => exact he _ v ht

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionSupportProof
