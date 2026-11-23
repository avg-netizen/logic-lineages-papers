module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionTargets

/-! `lem:arithmetic-accessibility`, components "I(Q) gives J({Q})" and "accessible members give J
of their multiset" (ordinals.tex 152–156), as internal ID₁ statements with their arithmetic as
explicit premises (Opus B, round 6; not a twin).

Printed: "Now I-induction on Q gives J({Q}): any replacement consists of finitely many
descendants Q_i, the induction hypothesis gives each J({Q_i}), and finite union gives the
replacement's membership. Another finite union proves the assertion for arbitrary accessible
member multisets."

Vocabulary beyond `ConditionalJUnionTargets`: `single sg q s` (s is the singleton multiset code of
q, by a program `sg`), `member mem x m` (x is a member of the multiset code m, by a program `mem`),
I = `membership false`, its carrier `carrier d false c` and R_S edge `edge d false c`.
"Consists of finitely many descendants … finite union" and "arbitrary member multisets" are
internalized as generation schemas: a property of codes that holds at the empty code and at the
singletons of the relevant elements and is closed under union holds at the code in question.
The schema bodies place the invariant θ at a bound variable by renaming. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJSingletonTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalJUnionTargets

/-- s is the singleton multiset code of q. -/
def single {α : Type} (sg : Program 1) (q s : OTerm α) : Formula α :=
  graph (OrdinaryArithmetic.graphFormula sg) s ![q]

/-- x is a member of the multiset code m. -/
def member {α : Type} (mem : Program 2) (x m : OTerm α) : Formula α :=
  graph (OrdinaryArithmetic.graphFormula mem) (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![x, m]

/-- θ is closed under union: ∀ m n o (θ m → θ n → U m n o → θ o). -/
def unionClosed {α : Type} (u : Program 2) (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  allOne (allOne (allOne
    ((θ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) (fun _ => Sum.inl (Sum.inl (Sum.inr 0))))).imp
      ((θ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) (fun _ => Sum.inl (Sum.inr 0)))).imp
        ((union u (.var (.inl (.inl (.inr 0)))) (.var (.inl (.inr 0))) (.var (.inr 0))).imp
          (θ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) (fun _ => Sum.inr 0))))))))

/-- θ holds at the singletons of the R_S-descendants of q: ∀ x t (edge q x → single x t → θ t). -/
def descendantSingletons {α : Type} (d : Data) (c : Nat) (sg : Program 1) (q : OTerm α)
    (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  allOne (allOne ((edge d false c ((q.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr 0)))).imp
    ((single sg (.var (.inl (.inr 0))) (.var (.inr 0))).imp
      (θ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun _ => Sum.inr 0))))))

/-- θ holds at the singletons of the members of m: ∀ x t (member x m → single x t → θ t). -/
def memberSingletons {α : Type} (mem : Program 2) (sg : Program 1) (m : OTerm α)
    (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  allOne (allOne ((member mem (.var (.inl (.inr 0))) ((m.relabel Sum.inl).relabel Sum.inl)).imp
    ((single sg (.var (.inl (.inr 0))) (.var (.inr 0))).imp
      (θ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun _ => Sum.inr 0))))))

/-- Arithmetic: the singleton of an I-carrier element is a J-carrier code. -/
def SingletonCarrier (d : Data) (c : Nat) (sg : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q s : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (carrier d false c q)) →
    Nonempty (Derivation (sourceBody d c) Γ (single sg q s)) →
    Nonempty (Derivation (sourceBody d c) Γ (carrier d true c s))

/-- Arithmetic: the empty code is a J-carrier code. -/
def NilCarrier (d : Data) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)),
    Nonempty (Derivation (sourceBody d c) Γ (carrier d true c (OrdinaryArithmetic.zeroTerm : OTerm α)))

/-- Arithmetic: no replacement step leaves the empty code. -/
def NilNoStep (d : Data) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (y : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (edge d true c OrdinaryArithmetic.zeroTerm y)) →
    Nonempty (Derivation (sourceBody d c) Γ ⊥)

/-- Arithmetic M7c: a replacement out of the singleton of q consists of finitely many
R_S-descendants of q, i.e. is generated from the empty code and their singletons by union. -/
def DescendantGeneration (d : Data) (c : Nat) (u : Program 2) (sg : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (θ : Formula (α ⊕ Fin 1)) (q s s' : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (instantiate θ (arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm))) →
    Nonempty (Derivation (sourceBody d c) Γ (descendantSingletons d c sg q θ)) →
    Nonempty (Derivation (sourceBody d c) Γ (unionClosed u θ)) →
    Nonempty (Derivation (sourceBody d c) Γ (single sg q s)) →
    Nonempty (Derivation (sourceBody d c) Γ (edge d true c s s')) →
    Nonempty (Derivation (sourceBody d c) Γ (instantiate θ (arithmeticEmbedding.onTerm s')))

/-- Arithmetic: every multiset code is generated from the empty code and the singletons of its
members by union. -/
def MemberGeneration (d : Data) (c : Nat) (u mem : Program 2) (sg : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (θ : Formula (α ⊕ Fin 1)) (m : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (instantiate θ (arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm))) →
    Nonempty (Derivation (sourceBody d c) Γ (memberSingletons mem sg m θ)) →
    Nonempty (Derivation (sourceBody d c) Γ (unionClosed u θ)) →
    Nonempty (Derivation (sourceBody d c) Γ (instantiate θ (arithmeticEmbedding.onTerm m)))

/-- I(q) gives J of the singleton of q. -/
def SingletonAccessibility (d : Data) (c : Nat) (sg : Program 1) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q s : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (membership false q)) →
    Nonempty (Derivation (sourceBody d c) Γ (single sg q s)) →
    Nonempty (Derivation (sourceBody d c) Γ (membership true s))

/-- Accessible members give J of their multiset. -/
def MembersAccessibility (d : Data) (c : Nat) (mem : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (m : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ
      (allOne ((member mem (.var (.inr 0)) (m.relabel Sum.inl)).imp (membership false (.var (.inr 0)))))) →
    Nonempty (Derivation (sourceBody d c) Γ (membership true m))

def ConditionalJSingleton : Prop :=
  ∀ (d : Data) (c : Nat) (u : Program 2) (sg : Program 1),
    CarrierUnion d c u → MultisetSplit d c u → SingletonCarrier d c sg → NilCarrier d c → NilNoStep d c →
    DescendantGeneration d c u sg → SingletonAccessibility d c sg

def ConditionalJMembers : Prop :=
  ∀ (d : Data) (c : Nat) (u mem : Program 2) (sg : Program 1),
    CarrierUnion d c u → MultisetSplit d c u → SingletonCarrier d c sg → NilCarrier d c → NilNoStep d c →
    DescendantGeneration d c u sg → MemberGeneration d c u mem sg → MembersAccessibility d c mem

end LogicLineages.PersistentMarking.ConditionalJSingletonTargets
