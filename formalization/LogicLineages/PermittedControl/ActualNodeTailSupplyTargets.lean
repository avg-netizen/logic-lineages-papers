module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNodeTailSupply
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualShortCountCleanup ActualZeroClassCommonTail ActualReadChargeIteration

/-- Only the original count tag contributes to the annotation bound;
neither coefficients, actual reads, annotations nor ρ are inputs. -/
def annotationBoundCode (op : LowerOperandCode) : Nat :=
  if op.1 = 2 then max (rawNormCode op.2.2.2.2.1) (rawNormCode op.2.2.2.2.2 + 3) else 0

def annotationTailCode (terms : List WeightedCode) : Nat :=
  finiteMax (fun t => annotationBoundCode t.2) terms

def annotationTail (terms : List WeightedOperand) : Nat :=
  annotationTailCode (terms.map encodeWeighted)

noncomputable def originalAnnotationBound : LowerOperand → Nat
  | .count _ lam mu => max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3)
  | _ => 0

def ExactAnnotationBoundCode : Prop :=
  ∀ op : LowerOperand, annotationBoundCode op.code = originalAnnotationBound op

/-- A single explicit bound for the present finite node only. The
second maximum is the existing #899 finite list/pair source bound. -/
noncomputable def nodeTail (B : Nat) (terms : List WeightedOperand) : Nat :=
  max (annotationTail terms) (commonTail B terms)

def PaidNodeTail (B : Nat) (ρ : Nat → Nat) (terms : List WeightedOperand) : Prop :=
  ∀ label ∈ prefixLabels terms, nodeTail B terms ≤ ρ label.rank

/-- The original LongField classification remains an input. Neither
long shape nor the needed paid tail follows from mere read success. -/
def ExactLongNodeGuards : Prop :=
  ∀ (B : Nat) (ρ : Nat → Nat) (xs : List Read),
    (∀ t ∈ xs.map Prod.fst, t.1 ≠ 0 → LongCountOperand t.2) →
    PaidNodeTail B ρ (xs.map Prod.fst) →
    NodeGuards B ρ xs

/-- Original checked grouping does not introduce a new operand or
change long shape. In particular the actual #908/#911 output can be
used as source, but its newly instantiated numeric bound is explicit. -/
def ExactNormalizedLongNodeGuards : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (source xs : List Read),
    liftedReads f ρ source →
    (∀ rd ∈ source, LongCountOperand rd.1.2) →
    normalizeReads f ρ source = some xs →
    PaidNodeTail B ρ (xs.map Prod.fst) →
    liftedReads f ρ xs ∧ (∀ rd ∈ xs, LongCountOperand rd.1.2) ∧ NodeGuards B ρ xs

def FullActualNodeTailSupply : Prop :=
  ExactAnnotationBoundCode ∧ ExactLongNodeGuards ∧ ExactNormalizedLongNodeGuards

end LogicLineages.PermittedControl.ActualNodeTailSupply
