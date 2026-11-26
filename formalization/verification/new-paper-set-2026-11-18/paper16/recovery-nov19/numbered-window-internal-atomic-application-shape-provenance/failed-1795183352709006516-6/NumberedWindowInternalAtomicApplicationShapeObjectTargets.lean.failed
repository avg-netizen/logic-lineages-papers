module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicApplicationShape

def freeTerm {α : Type} (t n : OTerm α) : OTerm α :=
  consTerm OrdinaryArithmetic.zeroTerm (consTerm t (consTerm n OrdinaryArithmetic.zeroTerm))

def bottomTerm {α : Type} (t : OTerm α) : OTerm α :=
  consTerm (numeral 3) (consTerm t OrdinaryArithmetic.zeroTerm)

def auxAddressTerm {α : Type} (c d e k a : OTerm α) : OTerm α :=
  let z : OTerm α := OrdinaryArithmetic.zeroTerm
  addressTerm c e (consTerm (numeral 6) (consTerm d (consTerm e (consTerm k (consTerm a z)))))

/-- The output of each actual fixed AST is characterized by a genuine
arithmetic equality, in arbitrary open object contexts. -/
def ExactOpenApplicationEmitters : Prop :=
  (∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (n c t k : OTerm α),
    let g := programGraph addressEmitter n ![c,t,k]
    let h := equal n (addressTerm c t k)
    Nonempty (Derivation B Γ (g.imp h ⊓ h.imp g))) ∧
  (∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (n c d e k a : OTerm α),
    let g := programGraph auxAddressEmitter n ![c,d,e,k,a]
    let h := equal n (auxAddressTerm c d e k a)
    Nonempty (Derivation B Γ (g.imp h ⊓ h.imp g)))

/-- Keep the given u/y, common packed c, and exact bare raw function k.
The four ordered eigenfields are domain, codomain, argument's raw
least field, result aux's raw right field. No equality between a/a'. -/
def literalApplicationShape {α : Type} (c t k u y : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 4 := Sum.inl
  let d : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let e : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let a : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let a' : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  block (equal (t.relabel j) (consTerm d e) ⊓
    (equal (u.relabel j) (addressTerm (c.relabel j) d a) ⊓
      equal (y.relabel j) (auxAddressTerm (c.relabel j) d e (k.relabel j) a')))

/-- True open acceptance by the new physical AST, with a literal free
or bottom function already given. Actual same u and y appear in the
shape, independently of numerical calibration. No output carrier. -/
def ExactOpenAtomicApplicationShape : Prop :=
  (∀ (p : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u y c t n : OTerm α),
    Nonempty (Derivation B Γ (equal f (packedFreeTerm c t n))) →
    Nonempty (Derivation B Γ (accepts (refinedApplication p) f u y)) →
    Nonempty (Derivation B Γ (literalApplicationShape c t (freeTerm t n) u y))) ∧
  (∀ (p : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u y c t : OTerm α),
    Nonempty (Derivation B Γ (equal f (packedBottomTerm c t))) →
    Nonempty (Derivation B Γ (accepts (refinedApplication p) f u y)) →
    Nonempty (Derivation B Γ (literalApplicationShape c t (bottomTerm t) u y)))

/-- A restricted, genuine arithmetic implication from the new branch
to the same old formula. No converse and no transfer of a derivation
mentioning an arbitrary changed h or changed sourceBody. -/
def ExactOpenApplicationForgets : Prop :=
  ∀ (p : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
    Nonempty (Derivation B Γ (accepts (refinedApplication p) f u y)) →
    Nonempty (Derivation B Γ (accepts p f u y))

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
