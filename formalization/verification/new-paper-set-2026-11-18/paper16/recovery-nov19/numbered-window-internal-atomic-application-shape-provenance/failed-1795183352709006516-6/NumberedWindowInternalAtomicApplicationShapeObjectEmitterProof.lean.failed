module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique outputTransport equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (z eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalAtomicApplicationShape NumberedWindowInternalAtomicApplicationShapeObjectTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairGraph {n : Nat} (p q : Program n) (x y : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation B Γ (programGraph p x xs)))
    (hq : Nonempty (Derivation B Γ (programGraph q y xs))) :
    Nonempty (Derivation B Γ (programGraph (consOf p q) (consTerm x y) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0))
    (consTerm x y) xs ![x,y] (consGraph x y)
  intro i
  exact Fin.cases hp (Fin.cases hq (fun k => Fin.elim0 k)) i

private theorem addressOver {n : Nat} (p q r : Program n) (c t k : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation B Γ (programGraph p c xs)))
    (hq : Nonempty (Derivation B Γ (programGraph q t xs)))
    (hr : Nonempty (Derivation B Γ (programGraph r k xs))) :
    Nonempty (Derivation B Γ (programGraph
      (consOf (literal n 3) (consOf p (consOf q (consOf r (zeroAt n))))) (addressTerm c t k) xs)) := by
  let e := zeroAt n
  let tag := literal n 3
  have nz : Nonempty (Derivation B Γ (programGraph e z xs)) := literalGraph 0 xs
  have g : Nonempty (Derivation B Γ (programGraph tag (numeral 3) xs)) := literalGraph 3 xs
  have a := pairGraph r e k z xs hr nz
  have b := pairGraph q (consOf r e) t (consTerm k z) xs hq a
  have d := pairGraph p (consOf q (consOf r e)) c (consTerm t (consTerm k z)) xs hp b
  exact pairGraph tag (consOf p (consOf q (consOf r e))) (numeral 3)
    (consTerm c (consTerm t (consTerm k z))) xs g d

theorem addressGraph (c t k : OTerm α) :
    Nonempty (Derivation B Γ (programGraph addressEmitter (addressTerm c t k) ![c,t,k])) := by
  let xs : Fin 3 → OTerm α := ![c,t,k]
  exact addressOver (.projection 0) (.projection 1) (.projection 2) c t k xs
    (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 2 xs)

theorem auxGraph (c d e k a : OTerm α) :
    Nonempty (Derivation B Γ (programGraph auxAddressEmitter (auxAddressTerm c d e k a) ![c,d,e,k,a])) := by
  let xs : Fin 5 → OTerm α := ![c,d,e,k,a]
  let pc : Program 5 := .projection 0
  let pd : Program 5 := .projection 1
  let pe : Program 5 := .projection 2
  let pk : Program 5 := .projection 3
  let pa : Program 5 := .projection 4
  let zz := zeroAt 5
  let tag := literal 5 6
  have gc : Nonempty (Derivation B Γ (programGraph pc c xs)) := projectionValue 0 xs
  have gd : Nonempty (Derivation B Γ (programGraph pd d xs)) := projectionValue 1 xs
  have ge : Nonempty (Derivation B Γ (programGraph pe e xs)) := projectionValue 2 xs
  have gk : Nonempty (Derivation B Γ (programGraph pk k xs)) := projectionValue 3 xs
  have ga : Nonempty (Derivation B Γ (programGraph pa a xs)) := projectionValue 4 xs
  have gz : Nonempty (Derivation B Γ (programGraph zz z xs)) := literalGraph 0 xs
  have gt : Nonempty (Derivation B Γ (programGraph tag (numeral 6) xs)) := literalGraph 6 xs
  let s₁ := consOf pa zz
  let s₂ := consOf pk s₁
  let s₃ := consOf pe s₂
  let s₄ := consOf pd s₃
  let s₅ := consOf tag s₄
  let t₁ := consTerm a z
  let t₂ := consTerm k t₁
  let t₃ := consTerm e t₂
  let t₄ := consTerm d t₃
  let t₅ := consTerm (numeral 6) t₄
  have h₁ : Nonempty (Derivation B Γ (programGraph s₁ t₁ xs)) := pairGraph pa zz a z xs ga gz
  have h₂ : Nonempty (Derivation B Γ (programGraph s₂ t₂ xs)) := pairGraph pk s₁ k t₁ xs gk h₁
  have h₃ : Nonempty (Derivation B Γ (programGraph s₃ t₃ xs)) := pairGraph pe s₂ e t₂ xs ge h₂
  have h₄ : Nonempty (Derivation B Γ (programGraph s₄ t₄ xs)) := pairGraph pd s₃ d t₃ xs gd h₃
  have h₅ : Nonempty (Derivation B Γ (programGraph s₅ t₅ xs)) := pairGraph tag s₄ (numeral 6) t₄ xs gt h₄
  exact addressOver pc pe s₅ c e t₅ xs gc ge h₅

section
attribute [local irreducible] programGraph

private theorem outputIff {n : Nat} (p : Program n) (xs : Fin n → OTerm α) (o expected : OTerm α)
    (known : ∀ Δ : List (Formula α), Nonempty (Derivation B Δ (programGraph p expected xs))) :
    Nonempty (Derivation B Γ ((programGraph p o xs).imp (equal o expected) ⊓
      (equal o expected).imp (programGraph p o xs))) := by
  let G := programGraph p o xs
  let E := eqn o expected
  rw [equalEqn]
  obtain ⟨forward⟩ := valueUnique (body := B) (Gamma := G :: Γ) p o expected xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (known _)
  obtain ⟨back⟩ := outputTransport (body := B) (Gamma := E :: Γ) p expected o xs
    ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (known _)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction back)⟩

theorem exactEmitters : ExactOpenApplicationEmitters :=
  ⟨fun _ _ _ n c t k => outputIff addressEmitter ![c,t,k] n (addressTerm c t k) (fun _ => addressGraph c t k),
   fun _ _ _ n c d e k a => outputIff auxAddressEmitter ![c,d,e,k,a] n (auxAddressTerm c d e k a)
     (fun _ => auxGraph c d e k a)⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
