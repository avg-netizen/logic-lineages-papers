module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorSuppliersDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorSuppliersTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open RankedPrecedenceCertificate SourceZeroNumberedComputability

/-- Every original primitive multiset witness gives literal nonempty direct
replacement by actual positive quotient paths, at the same finite window. -/
def ActualPrimitiveMultisetQuotientDescent : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (source target : List (Packed (Fin n) arity Gamma)),
    (∀ p ∈ source, InUniverse symbols S p.2) → PrimitiveMultiset source target →
    DirectMultisetPresentation.Direct (PositivePath (QuotientEdge n arity symbols S above Gamma))
      (source.map (representativeCode symbols S)) (target.map (representativeCode symbols S))

/-- Primary motion preserves ordinary shape, actual certified head rank and
its separate multiset of typed canonical base codes. -/
def ActualPrimaryOrdinaryMeasures : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) →
    ∀ (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
    rankCertificateTest table rank = true →
    ∀ (Gamma : List Ty) (f : Head (Fin n))
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (r : Packed (Fin n) arity Gamma),
    InUniverse symbols S (.ordinary f base) →
    WindowPrimary (Fin n) arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ r →
    ∃ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
      r = ⟨headResult g,.ordinary g base'⟩ ∧ headRank rank f = headRank rank g ∧
      (argumentCodes symbols S base).Perm (argumentCodes symbols S base')

/-- At arbitrary finite label, primary motion preserves the label, certified
head rank, base-code multiset and the exact ordered extra-code list separately. -/
def ActualPrimaryNumberedMeasures : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) →
    ∀ (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n),
    rankCertificateTest table rank = true →
    ∀ (Gamma : List Ty) (k : Nat) (f : Head (Fin n)) (tau : Ty)
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
      (r : Packed (Fin n) arity Gamma),
    InUniverse symbols S (.numbered k f tau base types extras) →
    WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ r →
    ∃ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g))
      (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      r = ⟨tau,.numbered k g tau base' types' extras'⟩ ∧ headRank rank f = headRank rank g ∧
      (argumentCodes symbols S base).Perm (argumentCodes symbols S base') ∧
      argumentCodes symbols S extras = argumentCodes symbols S extras'
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorSuppliersTargets
