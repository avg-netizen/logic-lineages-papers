module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRawUnionFromEquivalentPartsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginFinishProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (App Cmp exact_OriginalRawUnionFromEquivalentParts)

def Outcome (i : Program 1) (r : Program 3) (c : Nat) {α : Type} (Γ : List (Formula α))
    (changes : Bool) (source target witness removed : OTerm α) : Prop :=
  if changes then Pr (literalData i r) c Γ (certificate (literalData i r) true c source target witness)
  else target = source ∧ Pr (literalData i r) c Γ (eqn removed z)

/-- The actual four object cases conclude exactly the caller's original
continuation. For an unchanged side the original raw source term is
literally reused; the impossible all-empty case uses the genuine report. -/
theorem exact_OriginalCertifiedOriginFinish (i : Program 1) (r : Program 3) (c : Nat)
    {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)} (j : α → β)
    (left right dst : OTerm α) (goal : Formula α)
    (rawL rawR wl wr removedL removedR oldL oldR joined dl dr dt : OTerm β)
    (changedL changedR : Bool)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (bothNonempty : Pr (literalData i r) c Δ ((eqn removedL z ⊓ eqn removedR z).not))
    (dstParse : Pr (literalData i r) c Δ (unary parser (suc dt) (dst.relabel j)))
    (leftParse : Pr (literalData i r) c Δ (unary parser (suc dl) rawL))
    (rightParse : Pr (literalData i r) c Δ (unary parser (suc dr) rawR))
    (oldAppend : Pr (literalData i r) c Δ (App oldL oldR joined))
    (observed : Pr (literalData i r) c Δ (Cmp dt joined))
    (leftCount : Pr (literalData i r) c Δ (Cmp oldL dl))
    (rightCount : Pr (literalData i r) c Δ (Cmp oldR dr))
    (l : Outcome i r c Δ changedL (left.relabel j) rawL wl removedL)
    (r' : Outcome i r c Δ changedR (right.relabel j) rawR wr removedR)
    (split : SplitCases (literalData i r) c permutation Γ left right dst goal) :
    Pr (literalData i r) c Δ (goal.relabel j) := by
  have joined' := exact_OriginalRawUnionFromEquivalentParts rawL rawR (dst.relabel j)
    dl dr dt oldL oldR joined ⟨dstParse,leftParse,rightParse⟩ oldAppend observed leftCount rightCount
  cases changedL <;> cases changedR
  · obtain ⟨_,⟨eL⟩⟩ := l
    obtain ⟨_,⟨eR⟩⟩ := r'
    obtain ⟨no⟩ := bothNonempty
    exact ⟨Derivation.explosion (Derivation.implicationElimination no
      (Derivation.conjunctionIntroduction eL eR))⟩
  · obtain ⟨same,_⟩ := l
    rw [same] at joined'
    exact split.rightOnly β j Δ rawR wr keep r' joined'
  · obtain ⟨same,_⟩ := r'
    rw [same] at joined'
    exact split.leftOnly β j Δ rawL wl keep l joined'
  · exact split.both β j Δ rawL rawR wl wr keep l r' joined'

#print axioms exact_OriginalCertifiedOriginFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginFinishProof
