module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformInstanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof

/-! Syntax for the J-union double induction: the invariants as formula templates in their
term arguments, with substitution, instantiation and renaming lemmas (Opus B, round 6). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJUnionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst edgeSubst)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst bindSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (allsSubst liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding)
open ID1Completion.InternalSliceInductionSyntaxProof (anyFormulaRelabelAsSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (termRelabelAsSubst)
open ID1Completion.InternalTermSubstitutionSyntaxProof (formulaSubstComposition)
open ID1Completion.InternalBinderTransportSyntaxProof (formulaSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb eqn bindTerm bindEmbedding liftBind varBind)
open ConditionalUpperUniformInstanceProof (carrierSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalJUnionTargets

abbrev w {α : Type} : OTerm (α ⊕ Fin 1) := .var (.inr 0)
abbrev up {α : Type} (t : OTerm α) : OTerm (α ⊕ Fin 1) := t.relabel Sum.inl

/-- ∀ o (U m n o → J o). -/
def inner {α : Type} (u : Program 2) (m n : OTerm α) : Formula α :=
  allOne ((union u (up m) (up n) w).imp (membership true w))

/-- ∀ n (J n → inner m n). -/
def outer {α : Type} (u : Program 2) (m : OTerm α) : Formula α :=
  allOne ((membership true w).imp (inner u (up m) w))

/-- The strengthened inner invariant J n ∧ inner m n. -/
def innerInv {α : Type} (u : Program 2) (m n : OTerm α) : Formula α :=
  membership true n ⊓ inner u m n

/-- Outer induction hypothesis: ∀ m' (E m m' → outer m'). -/
def edgeOuter {α : Type} (d : Data) (c : Nat) (u : Program 2) (m : OTerm α) : Formula α :=
  allOne ((edge d true c (up m) w).imp (outer u w))

/-- Inner induction hypothesis: ∀ n' (E n n' → innerInv m n'). -/
def edgeInner {α : Type} (d : Data) (c : Nat) (u : Program 2) (m n : OTerm α) : Formula α :=
  allOne ((edge d true c (up n) w).imp (innerInv u (up m) w))

theorem allOneSubst {α β : Type} (phi : Formula (α ⊕ Fin 1)) (ts : α → ID1Completion.InternalCalculus.Term β) :
    (allOne phi).subst ts =
      allOne (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold allOne
  rw [allsSubst, bindSubst]

theorem unionSubst {α β : Type} (u : Program 2) (m n o : OTerm α) (ts : α → OTerm β) :
    (union u m n o).subst (fun a => emb (ts a)) = union u (m.subst ts) (n.subst ts) (o.subst ts) := by
  unfold union
  rw [graphSubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem innerSubst {α β : Type} (u : Program 2) (m n : OTerm α) (ts : α → OTerm β) :
    (inner u m n).subst (fun a => emb (ts a)) = inner u (m.subst ts) (n.subst ts) := by
  unfold inner
  rw [allOneSubst, liftedEmbedding]
  change allOne (((union u (up m) (up n) w).subst _).imp ((membership true w).subst _)) = _
  rw [unionSubst, membershipSubst, liftSubst, liftSubst]
  rfl

theorem outerSubst {α β : Type} (u : Program 2) (m : OTerm α) (ts : α → OTerm β) :
    (outer u m).subst (fun a => emb (ts a)) = outer u (m.subst ts) := by
  unfold outer
  rw [allOneSubst, liftedEmbedding]
  change allOne (((membership true w).subst _).imp ((inner u (up m) w).subst _)) = _
  rw [membershipSubst, innerSubst, liftSubst]
  rfl

theorem innerInvSubst {α β : Type} (u : Program 2) (m n : OTerm α) (ts : α → OTerm β) :
    (innerInv u m n).subst (fun a => emb (ts a)) = innerInv u (m.subst ts) (n.subst ts) := by
  unfold innerInv
  change (membership true n).subst _ ⊓ (inner u m n).subst _ = _
  rw [membershipSubst, innerSubst]

theorem edgeOuterSubst {α β : Type} (d : Data) (c : Nat) (u : Program 2) (m : OTerm α)
    (ts : α → OTerm β) :
    (edgeOuter d c u m).subst (fun a => emb (ts a)) = edgeOuter d c u (m.subst ts) := by
  unfold edgeOuter
  rw [allOneSubst, liftedEmbedding]
  change allOne (((edge d true c (up m) w).subst _).imp ((outer u w).subst _)) = _
  rw [edgeSubst, outerSubst, liftSubst]
  rfl

theorem edgeInnerSubst {α β : Type} (d : Data) (c : Nat) (u : Program 2) (m n : OTerm α)
    (ts : α → OTerm β) :
    (edgeInner d c u m n).subst (fun a => emb (ts a)) = edgeInner d c u (m.subst ts) (n.subst ts) := by
  unfold edgeInner
  rw [allOneSubst, liftedEmbedding]
  change allOne (((edge d true c (up n) w).subst _).imp ((innerInv u (up m) w).subst _)) = _
  rw [edgeSubst, innerInvSubst, liftSubst, liftSubst]
  rfl

/-! Instances at a term. -/

theorem innerBodyInstance {α : Type} (u : Program 2) (m n t : OTerm α) :
    instantiate ((union u (up m) (up n) w).imp (membership true w)) (emb t) =
      (union u m n t).imp (membership true t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((union u (up m) (up n) w).subst _).imp ((membership true w).subst _) = _
  rw [unionSubst, membershipSubst, liftBind, liftBind, varBind]

theorem outerBodyInstance {α : Type} (u : Program 2) (m t : OTerm α) :
    instantiate ((membership true w).imp (inner u (up m) w)) (emb t) =
      (membership true t).imp (inner u m t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((membership true w).subst _).imp ((inner u (up m) w).subst _) = _
  rw [membershipSubst, innerSubst, liftBind, varBind]

theorem edgeOuterInstance {α : Type} (d : Data) (c : Nat) (u : Program 2) (m t : OTerm α) :
    instantiate ((edge d true c (up m) w).imp (outer u w)) (emb t) =
      (edge d true c m t).imp (outer u t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((edge d true c (up m) w).subst _).imp ((outer u w).subst _) = _
  rw [edgeSubst, outerSubst, liftBind, varBind]

theorem edgeInnerInstance {α : Type} (d : Data) (c : Nat) (u : Program 2) (m n t : OTerm α) :
    instantiate ((edge d true c (up n) w).imp (innerInv u (up m) w)) (emb t) =
      (edge d true c n t).imp (innerInv u m t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((edge d true c (up n) w).subst _).imp ((innerInv u (up m) w).subst _) = _
  rw [edgeSubst, innerInvSubst, liftBind, liftBind, varBind]

/-- The membership atom as an instance of its open form. -/
theorem membershipInstance {α : Type} (t : OTerm α) :
    instantiate (membership true w) (emb t) = membership true t := by
  unfold instantiate
  rw [bindEmbedding, membershipSubst, varBind]

/-- The union graph with its first argument open. -/
theorem unionFirstInstance {α : Type} (u : Program 2) (n o t : OTerm α) :
    instantiate (union u w (up n) (up o)) (emb t) = union u t n o := by
  unfold instantiate
  rw [bindEmbedding, unionSubst, varBind, liftBind, liftBind]

/-! Renaming as substitution. -/

theorem relabelEmb {α β : Type} (phi : Formula α) (f : α → β) :
    phi.relabel f = phi.subst (fun a => emb (FirstOrder.Language.Term.var (f a) : OTerm β)) :=
  anyFormulaRelabelAsSubst phi f

theorem termRelabel {α β : Type} (t : OTerm α) (f : α → β) :
    t.subst (fun a => (FirstOrder.Language.Term.var (f a) : OTerm β)) = t.relabel f :=
  (termRelabelAsSubst t f).symm

theorem membershipRelabel {α β : Type} (x : OTerm α) (f : α → β) :
    (membership true x).relabel f = membership true (x.relabel f) := by
  rw [relabelEmb, membershipSubst, termRelabel]

theorem carrierRelabel {α β : Type} (d : Data) (c : Nat) (x : OTerm α) (f : α → β) :
    (carrier d true c x).relabel f = carrier d true c (x.relabel f) := by
  rw [relabelEmb, carrierSubst, termRelabel]

theorem edgeOuterRelabel {α β : Type} (d : Data) (c : Nat) (u : Program 2) (m : OTerm α) (f : α → β) :
    (edgeOuter d c u m).relabel f = edgeOuter d c u (m.relabel f) := by
  rw [relabelEmb, edgeOuterSubst, termRelabel]

theorem unionRelabel {α β : Type} (u : Program 2) (m n o : OTerm α) (f : α → β) :
    (union u m n o).relabel f = union u (m.relabel f) (n.relabel f) (o.relabel f) := by
  rw [relabelEmb, unionSubst, termRelabel, termRelabel, termRelabel]

theorem edgeRelabel {α β : Type} (d : Data) (c : Nat) (x y : OTerm α) (f : α → β) :
    (edge d true c x y).relabel f = edge d true c (x.relabel f) (y.relabel f) := by
  rw [relabelEmb, edgeSubst, termRelabel, termRelabel]

theorem edgeInnerRelabel {α β : Type} (d : Data) (c : Nat) (u : Program 2) (m n : OTerm α) (f : α → β) :
    (edgeInner d c u m n).relabel f = edgeInner d c u (m.relabel f) (n.relabel f) := by
  rw [relabelEmb, edgeInnerSubst, termRelabel, termRelabel]

theorem eqnRelabel {α β : Type} (s t : OTerm α) (f : α → β) :
    (eqn s t).relabel f = eqn (s.relabel f) (t.relabel f) := by
  rw [relabelEmb, ID1Completion.InternalTagArithmeticSyntaxProof.eqnSubst, termRelabel, termRelabel]

/-! Opening a universal quantifier at its own variable. -/

theorem allOneRelabel {α β : Type} (phi : Formula (α ⊕ Fin 1)) (f : α → β) :
    (allOne phi).relabel f = allOne (phi.relabel (Sum.map f id)) := by
  rw [anyFormulaRelabelAsSubst, allOneSubst, anyFormulaRelabelAsSubst]
  congr 2
  funext a
  cases a with
  | inl a => rfl
  | inr i => rfl

theorem selfInstance {α : Type} (phi : Formula (α ⊕ Fin 1)) :
    instantiate (phi.relabel (Sum.map Sum.inl id)) (FirstOrder.Language.Term.var (.inr 0)) = phi := by
  unfold instantiate
  rw [anyFormulaRelabelAsSubst, formulaSubstComposition]
  conv => rhs; rw [← formulaSubstVar phi]
  congr 1
  funext a
  cases a with
  | inl a => rfl
  | inr i => exact congrArg (fun j => (FirstOrder.Language.Term.var (Sum.inr j) : ID1Completion.InternalCalculus.Term (α ⊕ Fin 1))) (Subsingleton.elim 0 i)

end LogicLineages.PersistentMarking.ConditionalJUnionSyntaxProof
