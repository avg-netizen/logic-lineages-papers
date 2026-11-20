import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchDefinitions
import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.SourcePresentation
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt witnesses TypedProbeTotal)
open NumberedWindowInternalFreshProbeDispatch
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

abbrev SourceK := List LogicLineages.PersistentMarking.Ty

def ExactProbeTypeSupport : Prop :=
  ∀ (S : Spine.Signature) (K : SourceK) (t q : Nat), typed (fixed S K) t q = true →
    ∃ τ ∈ sourceWindow K, t = typeCode τ

def ExactProbeTypeCodeInjective : Prop := Function.Injective typeCode

def ExactProbeWindowChild : Prop :=
  ∀ (K : SourceK), DecisionSourceUniverse.Closed K → ∀ (σ τ : ProbeTy),
    LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ ∈ sourceWindow K → τ ∈ sourceWindow K

def ExactProbeVerifyCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : SourceK), DecisionSourceUniverse.Closed K →
    ∀ (l : Leaves), calibrated (fixed S K) l → ∀ (τ : ProbeTy) (q : Nat),
      evaluate (verify l τ) (q ::ᵥ nil) = (typed (fixed S K) (typeCode τ) q).toNat

def ExactProbeDispatchCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : SourceK), DecisionSourceUniverse.Closed K →
    ∀ (l : Leaves), calibrated (fixed S K) l → ∀ (t q : Nat),
      evaluate (dispatch l (sourceWindow K)) (t ::ᵥ q ::ᵥ nil) = (typed (fixed S K) t q).toNat

/-- Object graph equivalence, not standard-value equality. q and the
output are arbitrary free arithmetic terms. -/
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

/-- Give the exact original double-binder witness, with the literal fresh
and application-guard leaves and the SAME selected h at codomain. -/
def ExactProbeArrowBranch : Prop :=
  ∀ (l : Leaves) (W : List ProbeTy) (σ τ : ProbeTy), τ ∈ W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation body Γ (programGraph (verify l (.arrow σ τ)) (numeral 1) ![q])) →
      Nonempty (Derivation body Γ (witnesses l.applicationGuard (dispatch l W) l.fresh τ q))

def ExactProbeTypedTotal : Prop :=
  ∀ (l : Leaves) (K : SourceK), DecisionSourceUniverse.Closed K →
    ∀ (d : Data) (c : Nat), TypedProbeTotal d l.applicationGuard (dispatch l (sourceWindow K)) l.fresh c

/-- Preserve any already selected calibrated p and a, and pay the new h's
own exact valuation and object totality. -/
def ExactSelectedProbeTypedTotal : Prop :=
  ∀ (S : Spine.Signature) (K : SourceK), DecisionSourceUniverse.Closed K →
    ∀ (p : Program 3) (a : Program 1),
      (∀ q u v, evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph (fixed S K) q u v).toNat) →
      (∀ q, evaluate a (q ::ᵥ nil) = Encodable.encode (probe (fixed S K) q)) →
      ∃ h : Program 2,
        (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed (fixed S K) t q).toNat) ∧
        ∀ (d : Data) (c : Nat), TypedProbeTotal d p h a c

open NumberedWindowFunctionalGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)

/-- Preserve the exact #596 selected i,j,r,d,p and its original body/rules.
The calibrated original a and new calibrated h are chosen with that same p. -/
def ExactConcreteProbeTypedTotal : Prop :=
  ∀ (xs : Entries) (S : Spine.Signature) (K : SourceK), DecisionSourceUniverse.Closed K →
    let s := fixed S K
    ∃ (i j : Program 1) (r d p : Program 3) (h : Program 2) (a : Program 1),
      Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
      UniqueResult p ∧ InputGuards i j r d p ∧
      (∀ n, evaluate a (n ::ᵥ nil) = Encodable.encode (probe s n)) ∧
      (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
      ∀ c, TypedProbeTotal (data i j r d) p h a c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchTargets
