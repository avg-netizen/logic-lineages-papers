module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorBaseLabelTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalConstructorLabelStratumTargets
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalOddProgressiveInductionProof (oddLower)
open NumberedWindowInternalLiteralPackedJLexBlockTargets (lowerAt)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalConsUnionReportBuildProof (Report)

abbrev BaseFinite (α : Type) := FiniteMatrix (α ⊕ Fin 1)
abbrev BaseOrdinary (α : Type) := OrdinaryMatrix (α ⊕ Fin 1)

def baseLabelMotive {α : Type} (finite : BaseFinite α) (ordinary : BaseOrdinary α) :
    Formula (α ⊕ Fin 1) := labelStratum finite ordinary

def baseContext {α : Type} (i : Program 1) (r : Program 3) (c : Nat) (Γ : List (Formula α))
    (finite : BaseFinite α) (ordinary : BaseOrdinary α) : List (Formula (α ⊕ Fin 1)) :=
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  carrier (literalData i r) true c x ::
    oddLower (literalData i r) c x (baseLabelMotive finite ordinary) :: Γ.map weaken

/-- Object finite and ordinary progress at the current symbolic typed base.
The original smaller-base coordinate ranges over full label strata, so a
strict base step may choose a larger label, even the ordinary omega case. -/
def baseLabelProgress {α : Type} (i : Program 1) (r : Program 3) (c : Nat) (Γ : List (Formula α))
    (finite : BaseFinite α) (ordinary : BaseOrdinary α) : Prop :=
  Pr (literalData i r) c (baseContext i r c Γ finite ordinary)
    (finiteProgress finite ⊓ ordinaryProgress finite ordinary)

def ExactBaseLabelAtJ : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
      (base : OTerm α) (finite : BaseFinite α) (ordinary : BaseOrdinary α),
    Pr (literalData i r) c Γ (membership true base) →
    baseLabelProgress i r c Γ finite ordinary →
    Pr (literalData i r) c Γ (instantiate (baseLabelMotive finite ordinary) (emb base))

def ExactBaseLabelAtParsed : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
      (base scratch : OTerm α) (finite : BaseFinite α) (ordinary : BaseOrdinary α),
    Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![base] →
    Pr (literalData i r) c Γ (typedAt i scratch) →
    Pr (literalData i r) c Γ (scalarMembers scratch) →
    baseLabelProgress i r c Γ finite ordinary →
    Pr (literalData i r) c Γ (instantiate (baseLabelMotive finite ordinary) (emb base))

def ExactCertifiedLowerBaseLabel : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula (α ⊕ Fin 1)))
      (large small witness : OTerm (α ⊕ Fin 1)) (finite : BaseFinite α) (ordinary : BaseOrdinary α),
    Pr (literalData i r) c Γ (oddLower (literalData i r) c large (baseLabelMotive finite ordinary)) →
    Pr (literalData i r) c Γ (certificate (literalData i r) true c large small witness) →
    Pr (literalData i r) c Γ ((baseLabelMotive finite ordinary).subst (lowerAt small))

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorBaseLabelTargets
