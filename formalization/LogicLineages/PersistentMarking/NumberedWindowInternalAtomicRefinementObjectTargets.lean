module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement

def packedBottomTerm {α : Type} (c t : OTerm α) : OTerm α :=
  addressTerm c t (consTerm (numeral 3) (consTerm t OrdinaryArithmetic.zeroTerm))

/-- The actual selected emitter's graph, in arbitrary open arithmetic.
This is not evaluation of terms at an assignment. -/
def ExactOpenAtomicBottomEmitter : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out c t : OTerm α),
    let g := programGraph bottomEmitter out ![c,t]
    let e := equal out (packedBottomTerm c t)
    Nonempty (Derivation body Γ (g.imp e ⊓ e.imp g))

def sourceFields {α : Type} (x c t : OTerm α) : Formula α :=
  programGraph rawContext c ![x] ⊓ programGraph rawResult t ![x]

/-- Real graph reports from literal open atom shapes. The bottom branch
specifically checks that the earlier free test reports zero. -/
def ExactOpenAtomicRecognition : Prop :=
  (∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x c t n : OTerm α),
    Nonempty (Derivation body Γ (equal x (packedFreeTerm c t n))) →
    Nonempty (Derivation body Γ
      (programGraph freeSource (numeral 1) ![x] ⊓ sourceFields x c t))) ∧
  (∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x c t : OTerm α),
    Nonempty (Derivation body Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation body Γ
      (programGraph freeSource (numeral 0) ![x] ⊓ programGraph bottomSource (numeral 1) ![x])))

/-- From the same open refined checker on the same actual x/w/y,
extract y's exact bottom equality and actual scalar i graph. Bottom
acceptance produces genuine object falsum, not absence of a derivation
(an arbitrary hypothesis context might itself be inconsistent). -/
def ExactOpenRefinedAtomicAcceptance : Prop :=
  (∀ (i : Program 1) (r : Program 3) (body : Positive (Fin 1)) (α : Type)
     (Γ : List (Formula α)) (x w y c t n : OTerm α),
    Nonempty (Derivation body Γ (equal x (packedFreeTerm c t n))) →
    Nonempty (Derivation body Γ (programGraph (refined i r) (numeral 1) ![x,w,y])) →
    Nonempty (Derivation body Γ
      (equal y (packedBottomTerm c t) ⊓ programGraph i (numeral 1) ![y]))) ∧
  (∀ (i : Program 1) (r : Program 3) (body : Positive (Fin 1)) (α : Type)
     (Γ : List (Formula α)) (x w y c t : OTerm α),
    Nonempty (Derivation body Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation body Γ (programGraph (refined i r) (numeral 1) ![x,w,y])) →
    Nonempty (Derivation body Γ (⊥ : Formula α)))

/-- Same equations for the actual certificate and scalar carrier of
the NEW body. The original checker adapter retains its supplied
witness and maps [context,x,y,w] to [x,w,y].
No arbitrary old body transport or I/C assertion. -/
def ExactOpenRefinedAtomicCertificate : Prop :=
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
      (Γ : List (Formula α)) (x w y c t n : OTerm α),
    let S := data i j (refined i r) d
    let body := sourceBody S context
    Nonempty (Derivation body Γ (equal x (packedFreeTerm c t n))) →
    Nonempty (Derivation body Γ (certificate S false context x y w)) →
    Nonempty (Derivation body Γ (equal y (packedBottomTerm c t) ⊓ carrier S false context y))) ∧
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
      (Γ : List (Formula α)) (x w y c t : OTerm α),
    let S := data i j (refined i r) d
    let body := sourceBody S context
    Nonempty (Derivation body Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation body Γ (certificate S false context x y w)) →
    Nonempty (Derivation body Γ (⊥ : Formula α)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
