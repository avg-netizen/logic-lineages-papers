module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
/-- Dispatch alignment of actual source constructors and packed types from
one unchanged evaluator relation. Unknown raw tags are excluded by original
source admission, not by a caller-supplied tag range or constructor equality. -/
def ActualRoot : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter leftTag rightTag leftType rightType : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (EvaluatorAlignmentDefinitions.RootFields left parameter leftTag leftType)) →
 Nonempty (Derivation body Delta (EvaluatorAlignmentDefinitions.RootFields right parameter rightTag rightType)) →
 Nonempty (Derivation body Delta (equal leftTag rightTag ⊓ equal leftType rightType))

/-- Remove the common-domain/common-codomain requirement from the existing
application inverse-child supplier using actual independent selector fields. -/
def ActualApplication : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter ld lc lf la rd rc rf ra : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields left ld lc lf la)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields right rd rc rf ra)) →
 Nonempty (Derivation body Delta (equal ld rd ⊓ equal lc rc))

/-- Derive common binder types AND the actual extended parameter. No supplied
child admission, recursive output equality, or parameter equality is used. -/
def ActualLambda : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter ld lc child lp rd rc otherChild rp : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields left ld lc child parameter lp)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields right rd rc otherChild parameter rp)) →
 Nonempty (Derivation body Delta (equal ld rd ⊓ (equal lc rc ⊓ equal lp rp)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTargets
