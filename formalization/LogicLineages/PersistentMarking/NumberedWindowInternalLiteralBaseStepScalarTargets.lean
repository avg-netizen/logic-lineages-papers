module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (scalarMembers)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def ExactOpenLiteralBaseStepScalarMember : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
    (source target witness ds dt key : OTerm α),
    let data := literalData i r
    let B := sourceBody data c
    Pr data c Γ (certificate data true c source target witness) →
    Nonempty (Derivation B Γ (unary parser (suc ds) source)) →
    Nonempty (Derivation B Γ (unary parser (suc dt) target)) →
    Pr data c Γ (scalarMembers ds) →
    Nonempty (Derivation B Γ (memberGraph dt key)) →
    Pr data c Γ (membership false key)

def ExactOpenLiteralBaseStepScalarMembers : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
    (source target witness ds dt : OTerm α),
    let data := literalData i r
    let B := sourceBody data c
    Pr data c Γ (certificate data true c source target witness) →
    Nonempty (Derivation B Γ (unary parser (suc ds) source)) →
    Nonempty (Derivation B Γ (unary parser (suc dt) target)) →
    Pr data c Γ (scalarMembers ds) →
    Pr data c Γ (scalarMembers dt)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarTargets
