module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptance (branch constantZero)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)

def lambdaFragmentBodyCode : Program 1 :=
  .composition fragmentGuard (fun _ : Fin 1 => field 1)

def lambdaFragmentCheckedBase (B : Program 2) : Program 2 :=
  branch (normalize (onRaw lambdaFragmentBodyCode)) (constantZero 2) B

/-- Distinct restricted base. Pass the same B at nonmatching callbacks;
on the literal lambda branch positively require the real fragment report
at the original body selector. This is not generally calibrated as B. -/
def lambdaFragmentBase (B : Program 2) : Program 2 :=
  branch (onRaw (header 2 2)) B (lambdaFragmentCheckedBase B)

abbrev lambdaFragmentWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  lambdaLexicalWindow s (lambdaFragmentBase B) T

def ExactOpenCoverRestrictedLambdaFragmentBase : Prop :=
  ∀ (B : Program 2) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom q out : OTerm α),
    Nonempty (Derivation body Γ
      (programGraph (lambdaFragmentBase B) (suc out) ![ctx,lambdaTerm dom q])) →
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q))

def ExactOpenCoverRestrictedLambdaFragmentWindow : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx dom q out : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (lambdaFragmentWindow s B T) ctx out (lambdaTerm dom q))) →
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentTargets
