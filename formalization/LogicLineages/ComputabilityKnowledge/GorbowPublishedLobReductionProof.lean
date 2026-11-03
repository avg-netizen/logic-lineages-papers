module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof

@[expose] public section
/-! The actual Lob diagonal in the published D and the conditional Lob
reduction. The diagonal is the paid named fixed point of the literal Lob
template, with its numeral instance computed by composition, header and closed
substitution identities, then embedded into S and D by axiom membership.
The reduction uses only the displayed internal HB instances, the actual
D-proof certification for external necessitation and S/K Hilbert reasoning.
It does not prove that D satisfies HB2/HB3. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowFormulaSubstitution

/-! ### Hilbert combinators -/

private def liftK {T : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation T a) : Derivation T (.imp r a) :=
  .mp (.logical (.k a r)) p

private def compose {T : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation T (.imp b c)) (q : Derivation T (.imp a b)) : Derivation T (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftK a p)) q

private def mpUnder {T : Sentence → Prop} {n : Nat} {a x y : Formula n}
    (p : Derivation T (.imp a (.imp x y))) (q : Derivation T (.imp a x)) :
    Derivation T (.imp a y) :=
  .mp (.mp (.logical (.s a x y)) p) q

/-! ### Substitution identities for the Lob template -/

private theorem substNum {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute σ (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n σ k

private theorem substHeader {m n : Nat} (σ : Fin m → Term n) (arity tag : Nat)
    (as : List (Term m)) :
    GorbowSubstitution.substitute σ (GorbowRegistryTuple.headerTerm arity tag as) =
      GorbowRegistryTuple.headerTerm arity tag (as.map (GorbowSubstitution.substitute σ)) :=
  GorbowHeaderSubstitutionProof.headers m n σ arity tag as

/-- The implication-code term with its free sentence-code slot filled. -/
private theorem binInst (r d : Nat) :
    GorbowSubstitution.substitute (Fin.cases (Term.numeral d) Term.var : Fin 1 → Term 0)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.var 0) : Term 1) =
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral d) : Term 0) := by
  simp only [GorbowBooleanTruth.binaryCodeTerm, GorbowSubstitution.substitute, substHeader,
    List.map_cons, List.map_nil, substNum] <;> rfl

/-- A weakened closed sentence is unchanged by instantiating the fresh slot. -/
private theorem instClosed (theta : Sentence) (t : Term 0) :
    substituteFormula (Fin.cases t Term.var : Fin 1 → Term 0) (weakenClosed 1 theta) = theta := by
  unfold GorbowTheoryProof.weakenClosed
  rw [GorbowFormulaCompositionProof.composition]
  have he : (fun i : Fin 0 => GorbowSubstitution.substitute
      (Fin.cases t Term.var : Fin 1 → Term 0) ((Fin.elim0 : Fin 0 → Term 1) i)) =
      (Fin.elim0 : Fin 0 → Term 0) := funext fun i => Fin.elim0 i
  have h1 : substituteFormula (fun i : Fin 0 => GorbowSubstitution.substitute
      (Fin.cases t Term.var : Fin 1 → Term 0) ((Fin.elim0 : Fin 0 → Term 1) i)) theta =
      substituteFormula (Fin.elim0 : Fin 0 → Term 0) theta :=
    congrArg (fun f : Fin 0 → Term 0 => substituteFormula f theta) he
  exact h1.trans (GorbowClosedDeductionProof.closedSyntax.1 theta)

/-- The provability template at a sentence code is the literal Pr_D. -/
private theorem provInst (pF : Program 1) (c : GorbowPublishedDCB.Code) (sigma : Sentence) :
    substituteFormula
      (Fin.cases (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) Term.var :
        Fin 1 → Term 0) (provabilityTemplate pF c) =
      GorbowPublishedDCB.prD pF c sigma := by
  unfold provabilityTemplate GorbowPublishedDCB.prD GorbowPublishedDCB.applyProv
  rw [GorbowFormulaCompositionProof.composition]
  exact congrArg (fun f : Fin 1 → Term 0 =>
      substituteFormula f (GorbowPublishedDCB.provability pF c))
    (funext fun _ => binInst (GorbowSortedSyntaxCode.formulaCode (GorbowPublishedDCB.rho pF c))
      (GorbowSortedSyntaxCode.formulaCode sigma))

private theorem lobInstance (pF : Program 1) (c : GorbowPublishedDCB.Code) (theta sigma : Sentence) :
    GorbowStandardInstances.instantiate (lobTemplate pF c theta)
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) =
      .imp (GorbowPublishedDCB.prD pF c sigma) theta := by
  unfold GorbowStandardInstances.instantiate lobTemplate
  show Formula.imp
      (substituteFormula
        (Fin.cases (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) Term.var :
          Fin 1 → Term 0) (provabilityTemplate pF c))
      (substituteFormula
        (Fin.cases (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) Term.var :
          Fin 1 → Term 0) (weakenClosed 1 theta)) = _
  rw [provInst, instClosed]

/-! ### Embedding the named base into D -/

private theorem namedToD (pF pR : Program 1) (q : Program 5) (c : GorbowPublishedDCB.Code)
    (sigma : Sentence)
    (h : GorbowNamedDefiningTheory.Theory (GorbowPublishedDCB.augmented pF q) pR sigma) :
    GorbowPublishedDCB.D pF pR q c sigma :=
  Or.inl (List.mem_append.mpr (Or.inl h))

/-! ### The actual diagonal -/

theorem actualDiagonal : GorbowPublishedLobReduction.Targets.ActualDiagonal := by
  intro pF pR q c hA theta
  have hcal' := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  obtain ⟨hd⟩ := GorbowNamedDiagonalDerivation.Proof.fixedPoint
    (GorbowPublishedDCB.augmented pF q) pR hcal' (lobTemplate pF c theta)
  have hd' : Derivation (n := 0)
      (GorbowNamedDefiningTheory.Theory (GorbowPublishedDCB.augmented pF q) pR)
      (GorbowBooleanTruth.biconditional (delta pF c theta)
        (GorbowStandardInstances.instantiate (lobTemplate pF c theta)
          (Term.numeral (GorbowSortedSyntaxCode.formulaCode (delta pF c theta))))) := hd
  rw [lobInstance] at hd'
  exact GorbowTheoryProofProof.monotonicity _ (GorbowPublishedDCB.D pF pR q c)
    (namedToD pF pR q c) 0 _ ⟨hd'⟩

/-! ### The conditional Lob reduction -/

theorem localLobReduction : GorbowPublishedLobReduction.Targets.LocalLobReduction := by
  intro pF pR q c hA theta h1 h2 h3 hr
  obtain ⟨diag⟩ := actualDiagonal pF pR q c hA theta
  obtain ⟨hb1⟩ := h1
  obtain ⟨hb2'⟩ := h2
  obtain ⟨hb3'⟩ := h3
  obtain ⟨refl⟩ := hr
  -- The two directions of the actual diagonal biconditional.
  have e : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (delta pF c theta) (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta)) :=
    .mp (.logical (.andLeft _ _)) diag
  have er : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta) (delta pF c theta)) :=
    .mp (.logical (.andRight _ _)) diag
  -- External necessitation of the forward direction by actual D-proof certification.
  obtain ⟨cert1⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA
    (.imp (delta pF c theta) (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta)) ⟨e⟩
  -- First HB2 instance: Pr d → Pr (Pr d → theta).
  have a1 : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta))
        (GorbowPublishedDCB.prD pF c
          (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta))) :=
    .mp hb1 cert1
  -- Second HB2 instance composed: Pr d → (Pr Pr d → Pr theta).
  have a2 : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta))
        (.imp (GorbowPublishedDCB.prD pF c (GorbowPublishedDCB.prD pF c (delta pF c theta)))
          (GorbowPublishedDCB.prD pF c theta))) :=
    compose hb2' a1
  -- HB3 instance: Pr d → Pr Pr d, hence Pr d → Pr theta.
  have a3 : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta))
        (GorbowPublishedDCB.prD pF c theta)) :=
    mpUnder a2 hb3'
  -- With the supplied reflection Pr theta → theta: Pr d → theta.
  have v : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c)
      (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta) :=
    compose refl a3
  -- The reverse diagonal direction gives d, certification gives Pr d, then theta.
  have dd : Derivation (n := 0) (GorbowPublishedDCB.D pF pR q c) (delta pF c theta) :=
    .mp er v
  obtain ⟨cert2⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA
    (delta pF c theta) ⟨dd⟩
  exact ⟨.mp v cert2⟩

theorem globalLobReduction : GorbowPublishedLobReduction.Targets.GlobalLobReduction := by
  intro pF pR q c hA hHB2 hHB3 theta hr
  exact localLobReduction pF pR q c hA theta
    (hHB2 (delta pF c theta) (.imp (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta))
    (hHB2 (GorbowPublishedDCB.prD pF c (delta pF c theta)) theta)
    (hHB3 (delta pF c theta)) hr

theorem fullTarget : GorbowPublishedLobReduction.Targets.Target :=
  ⟨actualDiagonal, localLobReduction, globalLobReduction⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.Proof
