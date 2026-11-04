module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificatesTargets
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificatesProof
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaProof

@[expose] public section
/-! Concrete internal beta-entry certificates for the actual ordinary beta
formula. The translated closed formula is matched against the literal two-binder
matrix by exact syntax; its two closed arithmetic equalities have actual PA-core
proofs via the paid numeral calculation theorem, and the witnesses q, d are
introduced by the paid encoded-existential rule. The finite-sequence witness
comes from the paid ordinary beta/CRT construction. No beta, program or pairing
symbol, graph-correctness axiom, internal division theorem or HB is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.Proof
open GorbowSyntax GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

/-! ### Hilbert combinators (same pattern as the R024 private helpers) -/

private def idProof (A : Sentence → Prop) {n : Nat} (a : Formula n) : Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

private def liftP {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def sApp {A : Sentence → Prop} {n : Nat} {x y z : Formula n}
    (p : Derivation A (.imp x (.imp y z))) (q : Derivation A (.imp x y)) : Derivation A (.imp x z) :=
  .mp (.mp (.logical (.s x y z)) p) q

private def pairProof {A : Sentence → Prop} {x y : Sentence} (px : Derivation A x)
    (py : Derivation A y) :
    Derivation A (.imp (.imp x (.imp y GorbowArithmeticCompositionCertificates.falseFormula))
      GorbowArithmeticCompositionCertificates.falseFormula) :=
  sApp (sApp (idProof A (.imp x (.imp y GorbowArithmeticCompositionCertificates.falseFormula)))
    (liftP _ px)) (liftP _ py)

/-! ### Literal syntax of the translated beta graph -/

private def shape (A B I R Q D : Term 2) : Sentence :=
  GorbowArithmeticCompositionCertificates.encodedExists
    (.imp (.all (.imp
      (.imp (.imp (.equal A (.add (.mul Q (.succ (.mul (.succ I) B))) R))
        (.imp (.equal (.add R (.succ D)) (.succ (.mul (.succ I) B)))
          GorbowArithmeticCompositionCertificates.falseFormula))
        GorbowArithmeticCompositionCertificates.falseFormula)
      GorbowArithmeticCompositionCertificates.falseFormula))
      GorbowArithmeticCompositionCertificates.falseFormula)

private theorem shapeCongr {A A' B B' I I' R R' Q Q' D D' : Term 2}
    (hA : A = A') (hB : B = B') (hI : I = I') (hR : R = R') (hQ : Q = Q') (hD : D = D') :
    shape A B I R Q D = shape A' B' I' R' Q' D' := by
  subst hA hB hI hR hQ hD
  rfl

private theorem renameNumeral {m : Nat} (k : Nat) :
    GorbowFormulaSubstitution.renameTerm (Fin.succ : Fin m → Fin (m+1)) (Term.numeral k) =
      Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals _ _ _ k

private theorem freeLeaf {m : Nat} (σ : Fin m → Term 0) (j : Fin m) (k : Nat)
    (h : σ j = Term.numeral k) :
    GorbowSubstitution.substitute
      (GorbowFormulaSubstitution.liftSubstitute (GorbowFormulaSubstitution.liftSubstitute σ))
      (Term.var j.succ.succ) = Term.numeral k := by
  change GorbowFormulaSubstitution.renameTerm Fin.succ
    (GorbowFormulaSubstitution.renameTerm Fin.succ (σ j)) = _
  rw [h, renameNumeral, renameNumeral]

private theorem innerBound (j : Fin 1) :
    (Fin.lastCases (0 : Fin 5) (fun k => (Fin.elim0 k : Fin 4).succ) : Fin 1 → Fin 5) j = 0 := by
  refine Fin.lastCases ?_ (fun k => Fin.elim0 k) j
  exact Fin.lastCases_last

private theorem qIndex :
    (Fin.lastCases (0 : Fin 6) (fun j => ((Fin.lastCases (0 : Fin 5)
      (fun k => (Fin.elim0 k : Fin 4).succ) : Fin 1 → Fin 5) j).succ) : Fin 2 → Fin 6) 0 = 1 := by decide

private theorem dIndex :
    (Fin.lastCases (0 : Fin 6) (fun j => ((Fin.lastCases (0 : Fin 5)
      (fun k => (Fin.elim0 k : Fin 4).succ) : Fin 1 → Fin 5) j).succ) : Fin 2 → Fin 6) 1 = 0 := by decide
private theorem qLeaf (σ : Fin 4 → Term 0) :
    GorbowSubstitution.substitute
      (GorbowFormulaSubstitution.liftSubstitute (GorbowFormulaSubstitution.liftSubstitute σ))
      (Term.var ((Fin.lastCases (0 : Fin 6) (fun j => ((Fin.lastCases (0 : Fin 5)
        (fun k => (Fin.elim0 k : Fin 4).succ) : Fin 1 → Fin 5) j).succ) : Fin 2 → Fin 6) 0)) =
      (Term.var 1 : Term 2) := by
  rw [qIndex]
  rfl

private theorem dLeaf (σ : Fin 4 → Term 0) :
    GorbowSubstitution.substitute
      (GorbowFormulaSubstitution.liftSubstitute (GorbowFormulaSubstitution.liftSubstitute σ))
      (Term.var ((Fin.lastCases (0 : Fin 6) (fun j => ((Fin.lastCases (0 : Fin 5)
        (fun k => (Fin.elim0 k : Fin 4).succ) : Fin 1 → Fin 5) j).succ) : Fin 2 → Fin 6) 1)) =
      (Term.var 0 : Term 2) := by
  rw [dIndex]
  rfl

theorem literalBeta : GorbowArithmeticBetaCertificates.Targets.LiteralBeta := by
  intro a b i r
  have hA := freeLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j)) 0 a rfl
  have hB := freeLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j)) 1 b rfl
  have hI := freeLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j)) 2 i rfl
  have hR := freeLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j)) 3 r rfl
  have hQ := qLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j))
  have hD := dLeaf (fun j : Fin 4 => Term.numeral (![a, b, i, r] j))
  exact shapeCongr hA hB hI hR hQ hD

/-! ### Closed arithmetic equalities by the paid numeral calculation -/

private def stdI : Interpretation where
  universalRelation := fun _ => True
  universalFunction := fun x => x
  agents := fun _ => True
  knowledgeAll := fun _ => True
  knowledge := fun _ _ => True
  truth := fun _ => True

private theorem numeralArith {n : Nat} :
    ∀ k : Nat, GorbowStandardInstances.ArithmeticTerm (Term.numeral k : Term n)
  | 0 => .zero
  | k+1 => .succ (numeralArith k)

private theorem modulusArith (b i : Nat) :
    GorbowStandardInstances.ArithmeticTerm (modulus b i : Term 0) :=
  .succ (.mul (.succ (numeralArith i)) (numeralArith b))

private theorem equationOne (T : Sentence → Prop) (a b i r q : Nat)
    (hq : a = q * ((i+1)*b+1) + r) :
    Nonempty (Derivation T (.equal (Term.numeral a : Term 0)
      (.add (.mul (Term.numeral q) (modulus b i)) (Term.numeral r)))) := by
  obtain ⟨p⟩ := GorbowArithmeticDerivationProof.equalValues _ _ (numeralArith a)
    (.add (.mul (numeralArith q) (modulusArith b i)) (numeralArith r)) stdI (by
      simp only [Term.realize, numeral_realize, modulus]
      exact hq)
  exact GorbowTheoryProofProof.coreEmbedding T 0 _ p

private theorem equationTwo (T : Sentence → Prop) (b i r d : Nat)
    (hd : r + (d + 1) = (i+1)*b+1) :
    Nonempty (Derivation T (.equal (.add (Term.numeral r : Term 0) (.succ (Term.numeral d)))
      (modulus b i))) := by
  obtain ⟨p⟩ := GorbowArithmeticDerivationProof.equalValues _ _
    (.add (numeralArith r) (.succ (numeralArith d))) (modulusArith b i) stdI (by
      simp only [Term.realize, numeral_realize, modulus]
      exact hd)
  exact GorbowTheoryProofProof.coreEmbedding T 0 _ p

/-! ### Witness instances -/

private theorem matrixSubst {m n : Nat} (σ : Fin m → Term n) (a b i r : Nat) (Q D : Term m) :
    GorbowFormulaSubstitution.substituteFormula σ (matrix a b i r Q D) =
      matrix a b i r (GorbowSubstitution.substitute σ Q) (GorbowSubstitution.substitute σ D) := by
  have hn : ∀ k, GorbowSubstitution.substitute σ (Term.numeral k) = Term.numeral k :=
    fun k => GorbowHeaderSubstitutionProof.numerals _ _ σ k
  simp only [matrix, modulus, GorbowArithmeticCompositionCertificates.falseFormula,
    GorbowFormulaSubstitution.substituteFormula, GorbowSubstitution.substitute, hn]

private theorem matrixInstance (a b i r q d : Nat) :
    GorbowStandardInstances.instantiate
      (matrix a b i r (Term.numeral q) (.var 0) : Formula 1) (Term.numeral d : Term 0) =
      (matrix a b i r (Term.numeral q) (Term.numeral d) : Sentence) := by
  unfold GorbowStandardInstances.instantiate
  rw [matrixSubst]
  exact congrArg (fun Q => matrix a b i r Q (Term.numeral d))
    (GorbowHeaderSubstitutionProof.numerals _ _ _ q)

private theorem quotientInstance (a b i r q : Nat) :
    GorbowStandardInstances.instantiate (quotientBody a b i r) (Term.numeral q) =
      GorbowArithmeticCompositionCertificates.encodedExists
        (matrix a b i r (Term.numeral q) (.var 0)) := by
  have hm : GorbowFormulaSubstitution.substituteFormula
      (GorbowFormulaSubstitution.liftSubstitute (Fin.cases (Term.numeral q) Term.var : Fin 1 → Term 0))
      (matrix a b i r (.var 1) (.var 0)) = matrix a b i r (Term.numeral q) (.var 0) := by
    rw [matrixSubst]
    exact congrArg (fun Q => matrix a b i r Q (.var 0)) (renameNumeral q)
  exact congrArg (fun X : Formula 1 => (Formula.imp
    (.all (.imp X GorbowArithmeticCompositionCertificates.falseFormula))
    GorbowArithmeticCompositionCertificates.falseFormula : Sentence)) hm

private theorem entryProof (T : Sentence → Prop) (a b i r q d : Nat)
    (hq : a = q * ((i+1)*b+1) + r) (hd : r + (d + 1) = (i+1)*b+1) :
    Nonempty (Derivation T (GorbowArithmeticBetaCertificates.literalBeta a b i r)) := by
  obtain ⟨p1⟩ := equationOne T a b i r q hq
  obtain ⟨p2⟩ := equationTwo T b i r d hd
  have hm : Nonempty (Derivation (n:=0) T (GorbowStandardInstances.instantiate
      (matrix a b i r (Term.numeral q) (.var 0) : Formula 1) (Term.numeral d : Term 0))) := by
    rw [matrixInstance]
    exact ⟨pairProof p1 p2⟩
  have hx := GorbowArithmeticCompositionCertificates.Proof.witnessIntroduction T _ _ hm
  have hq' : Nonempty (Derivation T (GorbowStandardInstances.instantiate
      (quotientBody a b i r) (Term.numeral q))) := by
    rw [quotientInstance]
    exact hx
  exact GorbowArithmeticCompositionCertificates.Proof.witnessIntroduction T _ _ hq'

/-! ### The four clauses -/

theorem positiveBetaCertificates :
    GorbowArithmeticBetaCertificates.Targets.PositiveBetaCertificates := by
  intro T a b i r h
  have hlt : r < (i+1)*b+1 := by
    rw [← h]
    exact Nat.mod_lt a (Nat.succ_pos _)
  have hq : a = a / ((i+1)*b+1) * ((i+1)*b+1) + r := by
    rw [← h]
    have e := Nat.div_add_mod a ((i+1)*b+1)
    rw [Nat.mul_comm] at e
    exact e.symm
  have hd : r + ((i+1)*b+1 - (r+1) + 1) = (i+1)*b+1 := by
    generalize (i+1)*b+1 = M at hlt ⊢
    omega
  rw [literalBeta a b i r]
  exact entryProof T a b i r _ _ hq hd

private theorem valueDict (a b i r : Nat) :
    (fun j : Fin 4 => GorbowSubstitution.substitute (Fin.cases (Term.numeral r) Term.var : Fin 1 → Term 0)
      ((Fin.cases (Term.numeral a) (Fin.cases (Term.numeral b)
        (Fin.cases (Term.numeral i) (fun _ : Fin 1 => (.var 0 : Term 1)))) : Fin 4 → Term 1) j)) =
      (fun j : Fin 4 => Term.numeral (![a, b, i, r] j)) := by
  funext j
  cases j using Fin.cases with
  | zero => exact GorbowHeaderSubstitutionProof.numerals _ _ _ a
  | succ j =>
    cases j using Fin.cases with
    | zero => exact GorbowHeaderSubstitutionProof.numerals _ _ _ b
    | succ j =>
      cases j using Fin.cases with
      | zero => exact GorbowHeaderSubstitutionProof.numerals _ _ _ i
      | succ j =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact Fin.elim0 j

private theorem valueInstance (a b i r : Nat) :
    GorbowStandardInstances.instantiate (valueBody a b i) (Term.numeral r) = closedBeta a b i r :=
  (GorbowFormulaCompositionProof.composition _ _ _ _ _ _).trans
    (congrArg (fun s => GorbowFormulaSubstitution.substituteFormula s
      (GorbowOrdinaryArithmeticGraphs.translateBounded OrdinaryArithmetic.betaGraph id Fin.elim0))
      (valueDict a b i r))

theorem pointwiseValueTotality :
    GorbowArithmeticBetaCertificates.Targets.PointwiseValueTotality := by
  intro T a b i
  have h := positiveBetaCertificates T a b i (a % ((i+1)*b+1)) rfl
  rw [← valueInstance] at h
  exact GorbowArithmeticCompositionCertificates.Proof.witnessIntroduction T _ _ h

theorem finiteSequenceCertificates :
    GorbowArithmeticBetaCertificates.Targets.FiniteSequenceCertificates := by
  intro T n values
  obtain ⟨l, hl⟩ := values
  obtain ⟨a, b, h⟩ := OrdinaryArithmeticBetaProof.finiteSequenceWitness l
  refine ⟨a, b, fun i => positiveBetaCertificates T a b i.val _ ?_⟩
  have hi := h ⟨i.val, by rw [hl]; exact i.isLt⟩
  exact (OrdinaryArithmeticBetaProof.betaTermTruth
    (FirstOrder.Language.Term.var (0 : Fin 4) : OrdinaryArithmetic.Term (Fin 4))
    (FirstOrder.Language.Term.var (1 : Fin 4))
    (FirstOrder.Language.Term.var (2 : Fin 4))
    (FirstOrder.Language.Term.var (3 : Fin 4)) _).mp hi

theorem fullTarget : GorbowArithmeticBetaCertificates.Targets.Target :=
  ⟨literalBeta, positiveBetaCertificates, pointwiseValueTotality, finiteSequenceCertificates⟩

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.Proof
