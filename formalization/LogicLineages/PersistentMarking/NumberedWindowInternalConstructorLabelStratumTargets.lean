module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (allOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalStrongInduction (step)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalConsUnionReportBuildProof (Report)

/-- Literal later-coordinate slots: packed context, raw extra-argument list,
output type code, and output address. Typedness/compatibility, when needed,
are hypotheses of the supplied constructor matrices, below this binder. -/
abbrev Later := Fin 4

abbrev FiniteMatrix (α : Type) := Formula ((α ⊕ Fin 1) ⊕ Later)
abbrev OrdinaryMatrix (α : Type) := Formula (α ⊕ Later)

def finiteLabelBody {α : Type} (finite : FiniteMatrix α) : Formula (α ⊕ Fin 1) :=
  allBlock finite

def finiteLabels {α : Type} (finite : FiniteMatrix α) : Formula α :=
  allOne (finiteLabelBody finite)

def ordinaryLabel {α : Type} (ordinary : OrdinaryMatrix α) : Formula α :=
  allBlock ordinary

def finiteProgress {α : Type} (finite : FiniteMatrix α) : Formula α :=
  allOne (step (finiteLabelBody finite))

def ordinaryProgress {α : Type} (finite : FiniteMatrix α) (ordinary : OrdinaryMatrix α) : Formula α :=
  (finiteLabels finite).imp (ordinaryLabel ordinary)

def labelStratum {α : Type} (finite : FiniteMatrix α) (ordinary : OrdinaryMatrix α) : Formula α :=
  finiteLabels finite ⊓ ordinaryLabel ordinary

/-- Fixed admitted base; the progress hypotheses are literal object
formulas in the J-base context. The ordinary/omega case is separate,
not an extra numeral or a finite-label predecessor. -/
def ExactLabelStratumAtJBase : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat)
      (α : Type) (Γ : List (Formula α)) (base : OTerm α)
      (finite : FiniteMatrix α) (ordinary : OrdinaryMatrix α),
    Pr (literalData i r) c Γ (membership true base) →
    Pr (literalData i r) c (membership true base :: Γ) (finiteProgress finite) →
    Pr (literalData i r) c (membership true base :: Γ) (ordinaryProgress finite ordinary) →
    Pr (literalData i r) c Γ (labelStratum finite ordinary)

def ExactLabelStratumFromParsedBase : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat)
      (α : Type) (Γ : List (Formula α)) (base scratch : OTerm α)
      (finite : FiniteMatrix α) (ordinary : OrdinaryMatrix α),
    Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![base] →
    Pr (literalData i r) c Γ (typedAt i scratch) →
    Pr (literalData i r) c Γ (scalarMembers scratch) →
    Pr (literalData i r) c (membership true base :: Γ) (finiteProgress finite) →
    Pr (literalData i r) c (membership true base :: Γ) (ordinaryProgress finite ordinary) →
    Pr (literalData i r) c Γ (labelStratum finite ordinary)

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
