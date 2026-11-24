module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim zeroBranchIntro successorBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open GorbowVerifierNormalization (normalize)
open NumberedWindowInternalLiteralRootDispatchNumericProof (guard shapes route root)

attribute [local irreducible] programGraph

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

abbrev bit {α : Type} (p : Program 3) (xs : Fin 3 → OTerm α) : Formula α :=
  programGraph p (suc z) xs

/-- Original branch selection in finite object logic. A reached case
either accepts now or has a failed guard and uses the remaining branches.
No negative test concerns a different raw source or certificate. -/
def casesAt {α : Type} (leaf : Nat → Program 3) (xs : Fin 3 → OTerm α) : List (Nat × Nat) → Formula α
  | [] => ⊥
  | (tag,arity)::rest =>
    let G := bit (guard tag arity) xs
    (G ⊓ bit (leaf tag) xs) ⊔ (G.not ⊓ casesAt leaf xs rest)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem add {F : Formula α} (A : Formula α) (p : D B Γ F) : D B (A :: Γ) F :=
  p.map (Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h))

private def disjL {F G : Formula α} (p : Derivation B Γ F) : Derivation B Γ (F ⊔ G) := by
  apply Derivation.implicationIntroduction
  exact Derivation.explosion (Derivation.implicationElimination
    (Derivation.hypothesis List.mem_cons_self)
    (Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) p))

private def disjR {F G : Formula α} (p : Derivation B Γ G) : Derivation B Γ (F ⊔ G) :=
  Derivation.implicationIntroduction (Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) p)

theorem exact_OpenLiteralRoute (leaf : Nat → Program 3) (xs : Fin 3 → OTerm α)
    (cases : List (Nat × Nat)) :
    ∀ Γ : List (Formula α), D B Γ (bit (route leaf cases) xs) ↔ D B Γ (casesAt leaf xs cases) := by
  induction cases with
  | nil =>
    intro Γ
    change D B Γ (bit (constantZero 3) xs) ↔ D B Γ ⊥
    constructor
    · intro h
      obtain ⟨e⟩ := valueUnique (constantZero 3) (suc z) z xs h (constantZeroValue xs)
      exact ⟨sucNeZeroApply e⟩
    · rintro ⟨no⟩
      exact ⟨Derivation.explosion no⟩
  | cons p rest ih =>
    obtain ⟨tag,arity⟩ := p
    intro Γ
    let G := bit (guard tag arity) xs
    let L := bit (leaf tag) xs
    let R := casesAt leaf xs rest
    let lifted := route leaf rest
    let P := branch (normalize (guard tag arity)) lifted (leaf tag)
    change D B Γ (bit P xs) ↔ D B Γ ((G ⊓ L) ⊔ (G.not ⊓ R))
    constructor
    · intro known
      have success : D B (G :: Γ) L :=
        successorBranchElim (normalize (guard tag arity)) lifted (leaf tag) (suc z) z xs
          (normalizeAccept (guard tag arity) xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (add G known)
      have failure : D B (G.not :: Γ) (bit lifted xs) :=
        zeroBranchElim (normalize (guard tag arity)) lifted (leaf tag) (suc z) xs
          (normalizeReject (guard tag arity) xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (add G.not known)
      obtain ⟨s⟩ := success
      obtain ⟨f⟩ := (ih (G.not :: Γ)).1 failure
      exact ⟨disjunctionElimination (excludedMiddle G)
        (Derivation.implicationIntroduction (disjL
          (Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) s)))
        (Derivation.implicationIntroduction (disjR
          (Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) f)))⟩
    · rintro ⟨known⟩
      let A := G ⊓ L
      let C := G.not ⊓ R
      have ga : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
      have gf : Derivation B (C :: Γ) C := Derivation.hypothesis List.mem_cons_self
      obtain ⟨s⟩ := successorBranchIntro (normalize (guard tag arity)) lifted (leaf tag) (suc z) z xs
        (normalizeAccept (guard tag arity) xs ⟨Derivation.conjunctionLeft ga⟩)
        ⟨Derivation.conjunctionRight ga⟩
      obtain ⟨f⟩ := zeroBranchIntro (normalize (guard tag arity)) lifted (leaf tag) (suc z) xs
        (normalizeReject (guard tag arity) xs ⟨Derivation.conjunctionLeft gf⟩)
        ((ih (C :: Γ)).2 ⟨Derivation.conjunctionRight gf⟩)
      exact ⟨disjunctionElimination known (Derivation.implicationIntroduction s)
        (Derivation.implicationIntroduction f)⟩

/-- A caller with an arbitrary object goal can work in one exact
physical rule case at a time. This is the finite open split of the
literal root checker, not a numerical truth reflection principle. -/
theorem exact_OpenLiteralRootCaseElimination (leaf : Nat → Program 3) (xs : Fin 3 → OTerm α)
    (goal : Formula α) (held : D B Γ (bit (root leaf) xs))
    (next : ∀ tag arity, (tag,arity) ∈ shapes →
      ∀ Δ : List (Formula α), (∀ f ∈ Γ, f ∈ Δ) →
      D B Δ (bit (guard tag arity) xs) → D B Δ (bit (leaf tag) xs) → D B Δ goal) :
    D B Γ goal := by
  have start := (exact_OpenLiteralRoute (B := B) leaf xs shapes Γ).1 held
  have traverse (todo : List (Nat × Nat)) (sub : ∀ p ∈ todo, p ∈ shapes)
      (Δ : List (Formula α)) (keep : ∀ f ∈ Γ, f ∈ Δ)
      (h : D B Δ (casesAt leaf xs todo)) : D B Δ goal := by
    induction todo generalizing Δ with
    | nil =>
      obtain ⟨bad⟩ := h
      exact ⟨Derivation.explosion bad⟩
    | cons hd tl ih =>
      obtain ⟨tag,arity⟩ := hd
      let G := bit (guard tag arity) xs
      let L := bit (leaf tag) xs
      let A := G ⊓ L
      let C := G.not ⊓ casesAt leaf xs tl
      have a : Derivation B (A::Δ) A := Derivation.hypothesis List.mem_cons_self
      have c : Derivation B (C::Δ) C := Derivation.hypothesis List.mem_cons_self
      obtain ⟨finished⟩ := next tag arity (sub _ List.mem_cons_self) (A::Δ)
        (fun f h => List.mem_cons_of_mem _ (keep f h))
        ⟨Derivation.conjunctionLeft a⟩ ⟨Derivation.conjunctionRight a⟩
      obtain ⟨restProof⟩ := ih (fun p h => sub p (List.mem_cons_of_mem _ h)) (C::Δ)
        (fun f h => List.mem_cons_of_mem _ (keep f h)) ⟨Derivation.conjunctionRight c⟩
      obtain ⟨split⟩ := h
      exact ⟨disjunctionElimination split (Derivation.implicationIntroduction finished)
        (Derivation.implicationIntroduction restProof)⟩
  exact traverse shapes (fun _ h => h) Γ (fun _ h => h) start

#print axioms exact_OpenLiteralRoute
#print axioms exact_OpenLiteralRootCaseElimination
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
