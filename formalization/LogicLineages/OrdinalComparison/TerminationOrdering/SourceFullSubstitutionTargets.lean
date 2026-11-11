module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceFullSubstitution RankedPrecedenceCertificate

/-- The fundamental lemma for every original auxiliary constructor, using only
computable images at types in the fixed universe. -/
def ActualWindowComputableSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  WindowComputableEnvironment n arity Gamma Delta context ctx scalar theta →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q →
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute q theta⟩)

/-- Literal extension of the old applicative substitution contract: its
fragment restriction is removed and the certified precedence is made explicit. -/
def ActualFullComputableSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (tau : Ty) (v : Variable Gamma tau),
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,theta v⟩)) →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q →
    Computable n arity Delta (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute q theta⟩)

/-- The companion statement for all original argument lists. -/
def ActualArgumentComputableSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Delta context) (encodedR n arity Delta context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  WindowComputableEnvironment n arity Gamma Delta context ctx scalar theta →
  ∀ (types : List Ty) (args : AuxArguments (Fin n) arity Gamma types),
    NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) args →
    ∀ p ∈ argumentList (substituteArguments args theta),
      Computable n arity Delta (fun x => x ∈ leastSet scalar context) context p.1
        (representativeCode ctx.1.1 ctx.1.2 p)

/-- No fragment predicate, environment hypothesis, or condition on unused
source-context types remains in this all-term conclusion. -/
def ActualAllTermComputable : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q →
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

def ActualAllTermLeast : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q →
    representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩ ∈ leastSet scalar context

def ActualAllTermAccessible : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
  ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q →
    Acc (fun successor source => encodedR n arity Gamma context source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionTargets
