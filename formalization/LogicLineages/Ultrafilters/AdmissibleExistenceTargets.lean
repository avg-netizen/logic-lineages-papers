module

public import LogicLineages.Ultrafilters.ConvolutionDefinitions

@[expose] public section
namespace LogicLineages.Ultrafilters.Targets

/-- Exact source membership law, associativity, and continuity in the first
argument with the second argument fixed (not joint continuity). -/
def ConvolutionLaws : Prop :=
  (∀ (p q : Ultrafilter ℝ) (s : Set ℝ),
    s ∈ convolution p q ↔ {x | translate s x ∈ q} ∈ p) ∧
  (∀ p q r : Ultrafilter ℝ,
    convolution (convolution p q) r = convolution p (convolution q r)) ∧
  (∀ q : Ultrafilter ℝ, Continuous (fun p => convolution p q))

/-- All hypotheses needed to apply the compact-semigroup idempotent theorem
are conclusions, not premises. The subset is the unchanged actual NearZero. -/
def NearZeroCompactSemigroup : Prop :=
  ({p : Ultrafilter ℝ | NearZero p}).Nonempty ∧
  IsClosed {p : Ultrafilter ℝ | NearZero p} ∧
  IsCompact {p : Ultrafilter ℝ | NearZero p} ∧
  (∀ p q : Ultrafilter ℝ, NearZero p → NearZero q → NearZero (convolution p q))

/-- Nonvacuity supplier explicitly cited in paper 11; no idempotent or
near-zero ultrafilter is assumed. -/
def AdmissibleExistence : Prop := ∃ p : Ultrafilter ℝ, Admissible p

end LogicLineages.Ultrafilters.Targets
