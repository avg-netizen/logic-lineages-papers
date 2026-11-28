module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets

/-! Frozen targets for the type split of `lem:arithmetic-accessibility` at arrow types
(`CarrierTypingCases`, checkpoint 5 of the internal-accessibility plan; Fable B, 27 November 2026).

The selected checker `chosenH` certifies an arrow type by running the fresh selector, the binary
option application, the ternary application guard, and itself at the codomain. `CarrierTypingCases`
asks for that certificate from the scalar carrier alone. The statements below separate

* `LiteralProbeReports`: the open reports that the literal probe leaves supply
  (stored type in the finite window, prior typing, fresh selection, option output from an
  accepted application, carrier of an application result), from
* `FreshApplicationTotal`: the one remaining arithmetic fact, that the application of an admitted
  arrow address to its selected fresh address is accepted, with a result of the codomain type.

`TypingCasesFromReports` is the reduction of `CarrierTypingCases` to these two. Nothing here
asserts `FreshApplicationTotal`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped (chosenA chosenH)
open NumberedWindowInternalFreshProbeTargets (chosenAt)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt freshAt)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- The stored result field of the address `q` is the literal code of `τ`. -/
def storedType {α : Type} (τ : ProbeTy) (q : OTerm α) : Formula α :=
  programGraph rawResult (numeral (typeCode τ)) ![q]

/-- The finite disjunction of stored types over a literal window. Empty windows give falsity;
duplicate entries stay duplicate disjuncts. -/
def storedTypeChoices {α : Type} : List ProbeTy → OTerm α → Formula α
  | [], _ => ⊥
  | τ :: rest, q => storedType τ q ⊔ storedTypeChoices rest q

/-- Some accepted application result of `q` at `u` has stored type `τ`. Only the result is
bound; `q` and `u` stay free. -/
def typedResultAt {α : Type} (p : Program 3) (τ : ProbeTy) (q u : OTerm α) : Formula α :=
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 1)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (accepts p q' u' v ⊓ storedType τ v)

/-- The remaining arithmetic of the arrow branch. For an admitted address whose stored type is a
listed arrow type and for the fresh address selected for it, the installed application guard
accepts some result and that result has the codomain as stored type. -/
def FreshApplicationTotal (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (σ τ : ProbeTy), (.arrow σ τ : ProbeTy) ∈ W →
    ∀ (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
      Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (storedType (.arrow σ τ) q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (freshAt (chosenA A.probes) q u)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ
        (typedResultAt A.probes.applicationGuard τ q u))

/-- Results of accepted applications are scalar carriers. -/
def ApplicationResultCarrier (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (accepts A.probes.applicationGuard x u t)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c t))

/-- The open reports of the probe leaves that the typing branch consumes. Each field is a rule
about derivations in the installed body. -/
structure LiteralProbeReports (A : InstalledWindow S K W) (c : Nat) : Prop where
  /-- A carrier address stores one of the window's types. -/
  storedListed : ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (storedTypeChoices W q))
  /-- The prior type checker accepts a carrier address at its reported result field. -/
  priorIntro : ∀ (α : Type) (Γ : List (Formula α)) (t q : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (programGraph rawResult t ![q])) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.priorTyped (suc z) ![t, q]))
  /-- The fresh selector returns a successor at a carrier address of arrow type. -/
  freshIntro : ∀ (σ τ : ProbeTy) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (storedType (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (chosenAt (chosenA A.probes) q))
  /-- The binary option program reports the result of an accepted application. -/
  optionIntro : ∀ (α : Type) (Γ : List (Formula α)) (q u v : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (accepts A.probes.applicationGuard q u v)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.optionApplication (suc v) ![q, u]))
  /-- Results of accepted applications are scalar carriers. -/
  resultCarrier : ApplicationResultCarrier A c

/-- Every carrier address is typed by the selected checker at its own stored type. -/
def StoredTypeTyping (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ ρ ∈ W, ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (storedType ρ q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (typedAt (chosenH A.probes W) ρ q))

/-- Typing at the stored type, by external recursion on the type, from the probe reports and
the fresh application. -/
def StoredTypingFromReports (A : InstalledWindow S K (sourceWindow K)) (c : Nat) : Prop :=
  LiteralProbeReports A c → FreshApplicationTotal A c → StoredTypeTyping A c

/-- The milestone's type split from the probe reports and the fresh application. -/
def TypingCasesFromReports (A : InstalledWindow S K (sourceWindow K)) (c : Nat) : Prop :=
  LiteralProbeReports A c → FreshApplicationTotal A c → CarrierTypingCases A c

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingTargetsV2
