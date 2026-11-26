module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)

abbrev D {α : Type} (S : Data) (c : Nat) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation (sourceBody S c) Γ f)

/-- Open arithmetic shape test, using the checker's actual graph and
the literal accepting output. No extra predicate is added to ID₁. -/
def atom {α : Type} (test : Program 1) (x : OTerm α) : Formula α :=
  programGraph test (suc z) ![x]

/-- One original raw hop is checked by a different visible program from
the positive-path checker in S. All derivations still use sourceBody S c. -/
def directData (S : Data) (h : Program 3) : Data :=
  ⟨S.scalar,S.multiset,NumberedWindowCheckerCoordinates.suppliedCertificate h,S.direct⟩

def direct {α : Type} (S : Data) (h : Program 3) (c : Nat) (x y : OTerm α) : Formula α :=
  edge (directData S h) false c x y

/-- A nonempty accepted path has one genuine hop, followed either by
an identical endpoint or by an actual positive-path continuation. -/
def firstHop {α : Type} (S : Data) (h : Program 3) (c : Nat) (x y : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let m : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (direct S h c (x.relabel j) m ⊓
    (eqn m (y.relabel j) ⊔ edge S false c m (y.relabel j)))

def reducts {α : Type} (S : Data) (p h : Program 3) (c : Nat) (τ : Ty) (x : OTerm α) : Formula α :=
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((direct S h c (x.relabel Sum.inl) y).imp (formula p τ y))

/-- The same original argument and target appear in the fresh earlier
function's application. This is an object existential, not a
metatheoretic choice of a numeral. -/
def inherited {α : Type} (S : Data) (p h : Program 3) (c : Nat) (x u y : OTerm α) : Formula α :=
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (direct S h c (x.relabel Sum.inl) q ⊓ accepts p q (u.relabel Sum.inl) (y.relabel Sum.inl))

/-- Arithmetic inputs of the manuscript neutral lemma and atomic cases.
The acceptance and edge formulas are the original actual formulas.
These are hypotheses about open derivations, not merely numeric truth. -/
structure Arithmetic (S : Data) (p h : Program 3) (n b v : Program 1) (c : Nat) : Prop where
  pathFirstHop : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D S c Γ (edge S false c x y) → D S c Γ (firstHop S h c x y)
  directCarrier : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D S c Γ (direct S h c x y) → D S c Γ (carrier S false c y)
  bottomNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D S c Γ (atom b x) → D S c Γ (atom n x)
  bottomNoStep : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D S c Γ (atom b x) → D S c Γ (direct S h c x y) → D S c Γ ⊥
  variableNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D S c Γ (atom v x) → D S c Γ (atom n x)
  variableStep : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D S c Γ (atom v x) → D S c Γ (direct S h c x y) → D S c Γ (atom b y)
  applicationNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
    D S c Γ (atom n x) → D S c Γ (accepts p x u t) →
    D S c Γ (carrier S false c t) ∧ D S c Γ (atom n t)
  applicationInversion : ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    D S c Γ (atom n x) → D S c Γ (accepts p x u t) →
    D S c Γ (direct S h c t y) → D S c Γ (atom b y ⊔ inherited S p h c x u y)

structure FactsAt (S : Data) (p h : Program 3) (n b v : Program 1) (c : Nat) (τ : Ty) : Prop where
  neutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D S c Γ (carrier S false c x) → D S c Γ (atom n x) →
    D S c Γ (reducts S p h c τ x) → D S c Γ (formula p τ x)
  bottom : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D S c Γ (carrier S false c x) → D S c Γ (atom b x) → D S c Γ (formula p τ x)
  variableCase : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D S c Γ (carrier S false c x) → D S c Γ (atom v x) → D S c Γ (formula p τ x)

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
