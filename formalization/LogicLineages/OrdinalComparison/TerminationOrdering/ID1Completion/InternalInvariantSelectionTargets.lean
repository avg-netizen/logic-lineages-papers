module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionTargets
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof InternalCalculus JointGammaInvariant

/-- Arbitrary first-order formulas, including negative occurrences of P.
This is an internal proof of the ORIGINAL tagged formula's exact selection. -/
def ActualInternalInvariantSelection : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (scalar multiset : Formula (α ⊕ Fin 1))
    (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((instantiate (tagged scalar multiset) (arithmeticEmbedding.onTerm (tagTerm false t))).iff
      (instantiate scalar (arithmeticEmbedding.onTerm t)))) ∧
  Nonempty (Derivation body []
    ((instantiate (tagged scalar multiset) (arithmeticEmbedding.onTerm (tagTerm true t))).iff
      (instantiate multiset (arithmeticEmbedding.onTerm t))))

/-- The existing finite-S windowFormula, not a surrogate computability predicate. -/
def ActualInternalFiniteWindowSelection : Prop :=
  ∀ (source : SourcePresentation.Data) (context : Nat) (data : JointGammaComputability.Data)
    (S : List Ty) (multiset : Formula (Fin 2 ⊕ Fin 1)) (t : OrdinaryArithmetic.Term (Fin 2)),
  Nonempty (Derivation (SourcePresentation.sourceBody source context) []
    ((instantiate (tagged (window data S) multiset) (arithmeticEmbedding.onTerm (tagTerm false t))).iff
      (instantiate (window data S) (arithmeticEmbedding.onTerm t))))

/-- The ORIGINAL closure DERIVATION remains an explicit premise. Selecting
its conclusion does not manufacture this premise from standard-N semantics. -/
def ActualSelectedInvariantInduction : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (Gamma : List (Formula α))
    (scalar multiset : Formula (α ⊕ Fin 1)) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context)
    (replacedBody (SourcePresentation.sourceBody data context) (tagged scalar multiset) :: Gamma.map weaken)
    (tagged scalar multiset)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
    ((Positive.predicate (tagTerm false t)).formula.imp (instantiate scalar (arithmeticEmbedding.onTerm t)))) ∧
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
    ((Positive.predicate (tagTerm true t)).formula.imp (instantiate multiset (arithmeticEmbedding.onTerm t))))

/-- Conditional internal finite-S consequence, retaining precisely the original
combined-body closure obligation. No C_tau closure or positivity is asserted. -/
def ActualFiniteWindowInduction : Prop :=
  ∀ (source : SourcePresentation.Data) (context : Nat) (data : JointGammaComputability.Data)
    (S : List Ty) (Gamma : List (Formula (Fin 2)))
    (multiset : Formula (Fin 2 ⊕ Fin 1)) (t : OrdinaryArithmetic.Term (Fin 2)),
  Nonempty (Derivation (SourcePresentation.sourceBody source context)
    (replacedBody (SourcePresentation.sourceBody source context) (tagged (window data S) multiset) :: Gamma.map weaken)
    (tagged (window data S) multiset)) →
  Nonempty (Derivation (SourcePresentation.sourceBody source context) Gamma
    ((Positive.predicate (tagTerm false t)).formula.imp
      (instantiate (window data S) (arithmeticEmbedding.onTerm t))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionTargets
