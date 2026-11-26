module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.SourcePresentation
open NumberedWindowInternalProbeTargets (OTerm typeCode witnesses TypedProbeTotal)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeDispatchProgram

/-- All outputs and arbitrary free q. The compared formulas use the
actual original object compiler and the very same h and H ASTs. -/
def ExactProbeDispatchGraph : Prop :=
  ∀ (l : Leaves) (W : List ProbeTy) (τ : ProbeTy), τ ∈ W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out q : OTerm α),
      let h := programGraph (dispatch l W) out ![numeral (typeCode τ),q]
      let branch := programGraph (verify l τ) out ![q]
      Nonempty (Derivation body Γ (h.imp branch ⊓ branch.imp h))

def ExactProbeDispatchReject : Prop :=
  ∀ (l : Leaves) (W : List ProbeTy) (τ : ProbeTy), τ ∉ W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation body Γ
        (programGraph (dispatch l W) OrdinaryArithmetic.zeroTerm ![numeral (typeCode τ),q]))

def ExactProbeArrowBranch : Prop :=
  ∀ (l : Leaves) (W : List ProbeTy) (σ τ : ProbeTy), τ ∈ W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation body Γ (programGraph (verify l (.arrow σ τ)) (numeral 1) ![q])) →
      Nonempty (Derivation body Γ (witnesses l.applicationGuard (dispatch l W) l.fresh τ q))

/-- The literal introduction in #611, with no numerical calibration or
source-correctness premises used as rules. Type closure is external. -/
def ExactProbeTypedTotal : Prop :=
  ∀ (l : Leaves) (W : List ProbeTy), ChildClosed W →
    ∀ (d : Data) (c : Nat), TypedProbeTotal d l.applicationGuard (dispatch l W) l.fresh c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectTargets
