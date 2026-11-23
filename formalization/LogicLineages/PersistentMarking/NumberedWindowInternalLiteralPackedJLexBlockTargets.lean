module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOddProgressiveInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalOddProgressiveInductionProof (oddLower)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open ID1Completion.SourcePresentation (sourceBody)

/-- Substitute current and earlier coordinates while preserving every one
of the later, separately bound, first-order argument coordinates. -/
def specialize {α β : Type} {k : Nat} (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k))
    (σ : α ⊕ Fin 1 → Term β) : Formula (β ⊕ Fin k) :=
  matrix.subst (Sum.elim (fun a => (σ a).relabel Sum.inl) (fun i => .var (.inr i)))

def currentAt {α : Type} (raw : OTerm α) : α ⊕ Fin 1 → Term α :=
  Sum.elim Term.var (fun _ => emb raw)

/-- Outer free parameters are retained. The strictly smaller list is
substituted for the distinguished list coordinate in the invariant,
not for an outer parameter or one of the later arguments. -/
def lowerAt {α : Type} (small : OTerm (α ⊕ Fin 1)) : α ⊕ Fin 1 → Term (α ⊕ Fin 1) :=
  Sum.elim (fun a => .var (.inl a)) (fun _ => emb small)

def useLater {α β : Type} {k : Nat} (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k))
    (σ : α ⊕ Fin 1 → Term β) (later : Fin k → OTerm β) : Formula β :=
  (specialize matrix σ).subst (Sum.elim Term.var (fun j => emb (later j)))

def ExactOpenLiteralPackedJBlock : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (k : Nat) (Γ : List (Formula α))
    (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k)) (raw scratch : OTerm α),
    Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![raw] →
    Pr (literalData i r) c Γ (typedAt i scratch) →
    Pr (literalData i r) c Γ (scalarMembers scratch) →
    (let data := literalData i r
     let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
     Pr data c (carrier data true c x :: oddLower data c x (allBlock matrix) :: Γ.map weaken)
       (allBlock matrix)) →
    Pr (literalData i r) c Γ (allBlock (specialize matrix (currentAt raw)))

def ExactOpenLiteralPackedJLowerBlock : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (k : Nat)
    (Γ : List (Formula (α ⊕ Fin 1))) (matrix : Formula ((α ⊕ Fin 1) ⊕ Fin k))
    (large small witness : OTerm (α ⊕ Fin 1)),
    Pr (literalData i r) c Γ (oddLower (literalData i r) c large (allBlock matrix)) →
    Pr (literalData i r) c Γ (certificate (literalData i r) true c large small witness) →
    Pr (literalData i r) c Γ (allBlock (specialize matrix (lowerAt small)))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockTargets
