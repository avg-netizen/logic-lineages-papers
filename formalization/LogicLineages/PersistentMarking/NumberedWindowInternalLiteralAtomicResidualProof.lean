module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicNeutralStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicResidualProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic D atom direct inherited)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicNeutralStepProof
  (exact_OpenLiteralAtomicBottomNoStep exact_OpenLiteralAtomicVariableStep)
open NumberedWindowInternalLiteralNeutralResidualProof
  (Residual Body Step exact_LiteralArithmeticFromResidual)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (DirectRules)

/-- What remains of the neutral arithmetic after proving the genuine
direct-step clauses for both atoms. No positive application transport
or application shape theorem is included in this structure. -/
structure Remaining (s : Data) (p h : Program 3) (n : Program 1) (c : Nat) : Prop where
  bottomNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D s c Γ (atom bottomSource x) → D s c Γ (atom n x)
  variableNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D s c Γ (atom freeSource x) → D s c Γ (atom n x)
  applicationNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
    D s c Γ (atom n x) → D s c Γ (accepts p x u t) →
    D s c Γ (carrier s false c t) ∧ D s c Γ (atom n t)
  applicationInversion : ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    D s c Γ (atom n x) → D s c Γ (accepts p x u t) →
    D s c Γ (direct s h c t y) → D s c Γ (atom bottomSource y ⊔ inherited s p h c x u y)

abbrev AtomBody (i cv tv : Program 1) (raw : Program 5) (L : Program 3) :=
  Body i cv tv (guardedRaw raw) (guardedLeast L)

abbrev AtomStep (i cv tv : Program 1) (raw : Program 5) (L : Program 3) :=
  Step i cv tv (guardedRaw raw) (guardedLeast L)

theorem exact_LiteralAtomicResidual (i cv tv : Program 1) (raw : Program 5) (L p : Program 3)
    (n : Program 1) (c : Nat)
    (pending : Remaining (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) n c) :
    Residual (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) n bottomSource c :=
  ⟨pending.bottomNeutral,
    fun α Γ x y => exact_OpenLiteralAtomicBottomNoStep i cv tv raw L c x y,
    pending.variableNeutral,
    fun α Γ x y => exact_OpenLiteralAtomicVariableStep i cv tv raw L c x y,
    pending.applicationNeutral, pending.applicationInversion⟩

theorem exact_LiteralAtomicArithmetic (i cv tv : Program 1) (raw : Program 5) (L p : Program 3)
    (n : Program 1) (c : Nat)
    (rules : DirectRules i cv tv (guardedRaw raw) (guardedLeast L))
    (pending : Remaining (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) n c) :
    Arithmetic (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) n bottomSource freeSource c :=
  exact_LiteralArithmeticFromResidual i cv tv (guardedRaw raw) (guardedLeast L) p n bottomSource c
    rules (exact_LiteralAtomicResidual i cv tv raw L p n c pending)

#print axioms exact_LiteralAtomicResidual
#print axioms exact_LiteralAtomicArithmetic
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicResidualProof
