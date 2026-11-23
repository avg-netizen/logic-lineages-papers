module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

/-! `lem:arithmetic-accessibility`, component "J is closed under multiset union" (ordinals.tex
146–152), as an internal ID₁ statement over the accepted tagged presentation, with the two
arithmetic facts it uses as explicit premises (Opus B, round 6; not a twin).

Printed: "First prove closure of J under multiset union by outer J-induction on one component
and inner J-induction on the other. Label removed occurrences by their component of origin and
assign each new occurrence to a removed dominator. The target splits into two components, each
unchanged or decreased, with at least one decreased. The nested induction and downward closure
supply its J-membership."

Vocabulary: `J x := membership true x` (the odd-tag slice of the one ID₁ predicate),
`edge d true c` the direct multiset-replacement edge, `carrier d true c` its carrier, and the
union of list codes is the graph of an arbitrary program `u : Program 2` (`U m n o`: o is the
union of m and n).  The two premises are the arithmetic content of the printed argument. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJUnionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- o is the union of the list codes m and n, by the program u. -/
def union {α : Type} (u : Program 2) (m n o : OTerm α) : Formula α :=
  graph (OrdinaryArithmetic.graphFormula u) o ![m, n]

/-- The split clauses: each component unchanged or decreased, at least one decreased. -/
def splitBody {α : Type} (d : Data) (c : Nat) (u : Program 2) (m n o' m' n' : OTerm α) : Formula α :=
  union u m' n' o' ⊓
    (((edge d true c m m').not.imp (eqn m' m)) ⊓
      (((edge d true c n n').not.imp (eqn n' n)) ⊓
        ((edge d true c m m').not.imp (edge d true c n n'))))

/-- "The target splits into two components": ∃ m' n', splitBody. -/
def splitFormula {α : Type} (d : Data) (c : Nat) (u : Program 2) (m n o' : OTerm α) : Formula α :=
  existsOne (existsOne (splitBody d c u
    ((m.relabel Sum.inl).relabel Sum.inl) ((n.relabel Sum.inl).relabel Sum.inl)
    ((o'.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))))

/-- Arithmetic premise M7a: the union of two carrier codes is a carrier code. -/
def CarrierUnion (d : Data) (c : Nat) (u : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (m n o : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (carrier d true c m)) →
    Nonempty (Derivation (sourceBody d c) Γ (carrier d true c n)) →
    Nonempty (Derivation (sourceBody d c) Γ (union u m n o)) →
    Nonempty (Derivation (sourceBody d c) Γ (carrier d true c o))

/-- Arithmetic premise M7b: a direct replacement step out of a union splits. -/
def MultisetSplit (d : Data) (c : Nat) (u : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (m n o o' : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (union u m n o)) →
    Nonempty (Derivation (sourceBody d c) Γ (edge d true c o o')) →
    Nonempty (Derivation (sourceBody d c) Γ (splitFormula d c u m n o'))

/-- The conclusion: J is closed under the union. -/
def UnionClosure (d : Data) (c : Nat) (u : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (m n o : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (membership true m)) →
    Nonempty (Derivation (sourceBody d c) Γ (membership true n)) →
    Nonempty (Derivation (sourceBody d c) Γ (union u m n o)) →
    Nonempty (Derivation (sourceBody d c) Γ (membership true o))

def ConditionalJUnion : Prop :=
  ∀ (d : Data) (c : Nat) (u : Program 2), CarrierUnion d c u → MultisetSplit d c u → UnionClosure d c u

end LogicLineages.PersistentMarking.ConditionalJUnionTargets
