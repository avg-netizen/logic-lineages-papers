module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBTargets
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSelectedDistributionProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
/-! Proofs for the published sentence construction. S is presented by an
ordinary program computing its finite raw-axiom membership. rho is the paid
named diagonal of the printed reflection template. Pr_S is calibrated through
the actual named overlay at the embedded verifier's exact tag; S-proofs get
literal double-existential certificates from the named numeral derivations;
D-proofs are certified through actual closed deduction and the derived
implication-code equation. Selected reflection discharges closed premises,
keeps the agent free in context one and generalizes. No adequacy field,
semantic completeness inference or new proof constructor is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.Proof
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution List.Vector

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

private def weakenUnder {T : Sentence → Prop} {n : Nat} {a x : Formula n} (b : Formula n)
    (p : Derivation T (.imp a x)) : Derivation T (.imp a (.imp b x)) :=
  have hk : Derivation T (.imp x (.imp b x)) := .logical (.k x b)
  compose hk p

private theorem dischargeOne {T : Sentence → Prop} {R σ : Sentence}
    (h : Nonempty (Derivation (GorbowClosedDeduction.extend T R) σ)) :
    Nonempty (Derivation T (.imp R σ)) :=
  (GorbowClosedDeductionProof.closedExtension T R σ).mp h

/-! ### Derived existential introduction -/

private theorem refutation (T : Sentence → Prop) (P q : Sentence)
    (hi : Derivation T (.imp P (.neg q))) (hq : Derivation T q) :
    Nonempty (Derivation T (.neg P)) := by
  have hb : GorbowClassicalDerivation.contradictionBranch T (.neg P) (.neg (.neg P)) :=
    Or.inr rfl
  have hn : Derivation (GorbowClassicalDerivation.contradictionBranch T (.neg P))
      (.neg (.neg P)) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
      (Derivation.axiom (A := GorbowClassicalDerivation.contradictionBranch T (.neg P))
        (n := 0) (.neg (.neg P)) hb)
  obtain ⟨hp⟩ := GorbowClassicalDerivation.Proof.doubleNegationElimination _ P hn
  obtain ⟨hi'⟩ := GorbowTheoryProofProof.monotonicity T
    (GorbowClassicalDerivation.contradictionBranch T (.neg P))
    (fun _ hs => Or.inl hs) 0 _ ⟨hi⟩
  obtain ⟨hq'⟩ := GorbowTheoryProofProof.monotonicity T
    (GorbowClassicalDerivation.contradictionBranch T (.neg P))
    (fun _ hs => Or.inl hs) 0 _ ⟨hq⟩
  obtain ⟨hc⟩ := GorbowClassicalDerivation.Proof.explosion _ q (.neg P) hq' (.mp hi' hp)
  exact GorbowClassicalDerivation.Proof.closedReductio T (.neg P) hc

private theorem existsIntroduction (T : Sentence → Prop) (a : Formula 1) (t : Term 0)
    (h : Derivation T (GorbowStandardInstances.instantiate a t)) :
    Nonempty (Derivation T (.ex a)) := by
  have hi : Derivation T
      (.imp (.all (.neg a)) (.neg (GorbowStandardInstances.instantiate a t))) :=
    .logical (.allInstantiate (.neg a) t)
  obtain ⟨hn⟩ := refutation T (.all (.neg a)) (GorbowStandardInstances.instantiate a t) hi h
  exact ⟨.mp (.logical (.existsDualBackward a)) hn⟩

/-! ### Substitution identities -/

private theorem substNum {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute σ (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n σ k

private theorem substHeader {m n : Nat} (σ : Fin m → Term n) (arity tag : Nat)
    (as : List (Term m)) :
    GorbowSubstitution.substitute σ (GorbowRegistryTuple.headerTerm arity tag as) =
      GorbowRegistryTuple.headerTerm arity tag (as.map (GorbowSubstitution.substitute σ)) :=
  GorbowHeaderSubstitutionProof.headers m n σ arity tag as

private theorem substituteCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    GorbowSubstitution.substitute sigma (GorbowPRDefiningEquations.call tag args) =
      GorbowPRDefiningEquations.call tag (args.map (GorbowSubstitution.substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem liftVariables (n : Nat) :
    liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (φ : Formula n) : substituteFormula Term.var φ = φ := by
  induction φ with
  | equal t u | knowledge t u =>
    simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
    simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | neg φ ih => simp only [substituteFormula, ih]
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ => simp only [substituteFormula, hφ, hψ]
  | all φ ih | ex φ ih => simp only [substituteFormula, liftVariables, ih]

private theorem openInstance {T : Sentence → Prop} (B : Formula 1)
    (h : Derivation T (weakenClosed 1 (.all B))) : Nonempty (Derivation T B) := by
  have h' : Derivation T
      (.all (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)) := h
  have r := Derivation.mp (Derivation.logical (A := T)
    (.allInstantiate (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)
      (Term.var 0))) h'
  have hv : (fun i : Fin 1 => GorbowSubstitution.substitute
      (Fin.cases (Term.var 0) Term.var : Fin 2 → Term 1)
      (liftSubstitute (Fin.elim0 : Fin 0 → Term 1) i)) = Term.var := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  have he : GorbowStandardInstances.instantiate
      (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B) (Term.var 0) = B := by
    unfold GorbowStandardInstances.instantiate
    rw [GorbowFormulaCompositionProof.composition]
    rw [hv, formulaVariables]
  exact ⟨he ▸ r⟩

private theorem liftGuard (k : Nat) :
    weakenClosed 1 (GorbowBooleanTruth.sentenceGuard (Term.numeral k : Term 0)) =
      GorbowBooleanTruth.sentenceGuard (Term.numeral k : Term 1) := by
  simp only [weakenClosed, GorbowBooleanTruth.sentenceGuard, substituteFormula, substHeader,
    List.map_cons, List.map_nil, substNum]

private theorem liftBin (r s : Nat) :
    GorbowSubstitution.substitute (Fin.elim0 : Fin 0 → Term 1)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 0) =
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1) := by
  simp only [GorbowBooleanTruth.binaryCodeTerm, GorbowSubstitution.substitute, substHeader,
    List.map_cons, List.map_nil, substNum]

private theorem liftNumeralSucc (k : Nat) :
    liftSubstitute (Fin.cases (Term.numeral k) Term.var : Fin 1 → Term 0) (1 : Fin 2) =
      Term.numeral k :=
  substNum (fun i : Fin 0 => (Term.var i.succ : Term 1)) k

private theorem liftTwoNumeral (k : Nat) :
    liftSubstitute (liftSubstitute (fun _ : Fin 1 => (Term.numeral k : Term 0))) (2 : Fin 3) =
      Term.numeral k := by
  show GorbowSubstitution.substitute (fun i : Fin 1 => (Term.var i.succ : Term 2))
    (GorbowSubstitution.substitute (fun i : Fin 0 => (Term.var i.succ : Term 1))
      (Term.numeral k)) = _
  rw [substNum, substNum]

private theorem instantiateProv (pF : GorbowPRProgram.Program 1) (c : Code) (t : Term 0) :
    GorbowStandardInstances.instantiate (provability pF c) t = applyProv pF c t := by
  have hσ : (Fin.cases t Term.var : Fin 1 → Term 0) = (fun _ : Fin 1 => t) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  unfold GorbowStandardInstances.instantiate applyProv
  exact congrArg (fun σ : Fin 1 → Term 0 => substituteFormula σ (provability pF c)) hσ

/-! ### Theory embeddings -/

private theorem namedToS (pF pR : GorbowPRProgram.Program 1) (q : GorbowPRProgram.Program 5)
    (σ : Sentence) (h : GorbowNamedDefiningTheory.Theory (augmented pF q) pR σ) :
    S pF pR q σ :=
  List.mem_append.mpr (Or.inl h)

private theorem sdToS (pF pR : GorbowPRProgram.Program 1) (q : GorbowPRProgram.Program 5)
    (σ : Sentence) (h : GorbowSelectedDistribution.Theory (augmented pF q) pR σ) :
    S pF pR q σ := by
  rcases h with h | h
  · exact List.mem_append.mpr (Or.inl h)
  · subst h
    exact List.mem_append.mpr (Or.inr (by simp))

/-! ### Finite presentation of S -/

private theorem primitiveFiniteMembership (codes : List (List Nat)) :
    Primrec (fun raw : List Nat => decide (raw ∈ codes)) := by
  induction codes with
  | nil => simpa using (Primrec.const false : Primrec (fun _ : List Nat => false))
  | cons code codes ih =>
      have hd := Primrec.or.comp (Primrec.eq.comp (Primrec.id : Primrec (fun x : List Nat => x))
        (Primrec.const code)).decide ih
      exact hd.of_eq (fun raw => by simp; rfl)

private theorem checkPrimitive (pF pR : GorbowPRProgram.Program 1) (q : GorbowPRProgram.Program 5) :
    Primrec (checkS pF pR q) :=
  primitiveFiniteMembership ((axiomsS pF pR q).map GorbowFormulaPrefixCode.encode)

private theorem boolValue : Primrec (fun b : Bool => if b then (1 : Nat) else 0) :=
  (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq (fun b => by cases b <;> rfl)

private theorem indexComputable (pF pR : GorbowPRProgram.Program 1)
    (q : GorbowPRProgram.Program 5) :
    Computable (fun n : Nat =>
      if checkS pF pR q (Denumerable.ofNat (List Nat) n) then (1 : Nat) else 0) :=
  (boolValue.comp ((checkPrimitive pF pR q).comp (Primrec.ofNat (List Nat)))).to_comp

theorem finiteSPresentation : GorbowPublishedDCB.Targets.FiniteSPresentation := by
  intro pF pR q
  refine ⟨checkPrimitive pF pR q, ?_⟩
  obtain ⟨code, hcode⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp (indexComputable pF pR q).partrec)
  refine ⟨code, ?_⟩
  funext sigma
  apply propext
  show 1 ∈ Nat.Partrec.Code.eval code (Encodable.encode (GorbowFormulaPrefixCode.encode sigma)) ↔
    sigma ∈ axiomsS pF pR q
  rw [hcode]
  change 1 ∈ Part.some (if checkS pF pR q (Denumerable.ofNat (List Nat)
    (Encodable.encode (GorbowFormulaPrefixCode.encode sigma))) then 1 else 0) ↔ _
  rw [Denumerable.ofNat_encode, Part.mem_some_iff]
  have hiff : GorbowFormulaPrefixCode.encode sigma ∈
      (axiomsS pF pR q).map GorbowFormulaPrefixCode.encode ↔ sigma ∈ axiomsS pF pR q :=
    List.mem_map_of_injective (GorbowFormulaPrefixCodeProof.encodingInjective 0)
  by_cases h : sigma ∈ axiomsS pF pR q
  · rw [show checkS pF pR q (GorbowFormulaPrefixCode.encode sigma) = true from
      decide_eq_true (hiff.mpr h)]
    exact iff_of_true rfl h
  · rw [show checkS pF pR q (GorbowFormulaPrefixCode.encode sigma) = false from
      decide_eq_false (fun hm => h (hiff.mp hm))]
    exact iff_of_false (by simp) h

theorem actualParameters : GorbowPublishedDCB.Targets.ActualParameters := by
  obtain ⟨_, _, pF, pR, hF, hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  obtain ⟨q, hq⟩ := GorbowEnumeratedProvability.Proof.fixedUniversalProgram
  obtain ⟨c, hc⟩ := (finiteSPresentation pF pR q).2
  exact ⟨pF, pR, q, c, ⟨hF, hR⟩, hq, hc⟩

/-! ### The published diagonal sentence -/

theorem publishedDiagonal : GorbowPublishedDCB.Targets.PublishedDiagonal := by
  intro pF pR q c hcal
  have hcal' := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hcal
  have hd := GorbowNamedDiagonalDerivation.Proof.fixedPoint (augmented pF q) pR hcal'
    (reflectionTemplate pF c)
  exact GorbowTheoryProofProof.monotonicity _ (S pF pR q) (namedToS pF pR q) 0 _ hd

/-! ### Standard semantics of Pr_S -/

private theorem realizeProvCall (pF pR : GorbowPRProgram.Program 1) (q : GorbowPRProgram.Program 5)
    (c : Code) (I : Interpretation) (formula fuel cert : Nat) :
    (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (Term.numeral (Encodable.encode c) ::ᵥ Term.var 1 ::ᵥ Term.numeral 0 ::ᵥ Term.var 2 ::ᵥ
        Term.var 0 ::ᵥ List.Vector.nil : List.Vector (Term 3) 5)).realize
      (GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I)
      (Fin.cases cert (Fin.cases fuel (fun _ : Fin 1 => formula))) =
      GorbowPRProgram.evaluate q (GorbowEnumeratedProvability.arguments c fuel 0 formula cert) := by
  rw [GorbowNamedRegistryInterpretation.Proof.internalTerm 3 (augmented pF q) pR
    (GorbowNamedInternalProvability.checkerTag pF) 5 q
    (Term.numeral (Encodable.encode c) ::ᵥ Term.var 1 ::ᵥ Term.numeral 0 ::ᵥ Term.var 2 ::ᵥ
      Term.var 0 ::ᵥ List.Vector.nil) I
    (Fin.cases cert (Fin.cases fuel (fun _ : Fin 1 => formula)))
    (GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q)]
  simp only [List.Vector.map_cons, List.Vector.map_nil, numeral_realize,
    GorbowEnumeratedProvability.arguments] <;> rfl

private theorem provRealize (pF pR : GorbowPRProgram.Program 1) (q : GorbowPRProgram.Program 5)
    (c : Code) (I : Interpretation) (formula : Nat) :
    (applyProv pF c (Term.numeral formula)).realize
      (GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I) Fin.elim0 ↔
    ∃ fuel cert, GorbowPRProgram.evaluate q
      (GorbowEnumeratedProvability.arguments c fuel 0 formula cert) = 1 := by
  rw [applyProv, GorbowFormulaSubstitution.substituteFormula_realize]
  simp only [numeral_realize]
  apply exists_congr
  intro fuel
  apply exists_congr
  intro cert
  show (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (Term.numeral (Encodable.encode c) ::ᵥ Term.var 1 ::ᵥ Term.numeral 0 ::ᵥ Term.var 2 ::ᵥ
        Term.var 0 ::ᵥ List.Vector.nil : List.Vector (Term 3) 5)).realize
      (GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I)
      (Fin.cases cert (Fin.cases fuel (fun _ : Fin 1 => formula))) =
    (Term.numeral 1 : Term 3).realize
      (GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I)
      (Fin.cases cert (Fin.cases fuel (fun _ : Fin 1 => formula))) ↔ _
  rw [realizeProvCall, numeral_realize]

theorem provabilityCalibration : GorbowPublishedDCB.Targets.ProvabilityCalibration := by
  intro pF pR q c hA I formula
  obtain ⟨_, hq, hc⟩ := hA
  rw [provRealize]
  have h1 : (∃ fuel cert, GorbowPRProgram.evaluate q
      (GorbowEnumeratedProvability.arguments c fuel 0 formula cert) = 1) ↔
      ∃ fuel cert, GorbowEnumeratedProvability.check (c, fuel) 0 formula cert = true := by
    apply exists_congr
    intro fuel
    apply exists_congr
    intro cert
    rw [hq c fuel 0 formula cert]
    cases GorbowEnumeratedProvability.check (c, fuel) 0 formula cert <;> simp
  rw [h1, GorbowEnumeratedProvability.Proof.exactNumericAcceptance c 0 formula, hc]

/-! ### Literal Pr_S certificates -/

private def outerMatrix (pF : GorbowPRProgram.Program 1) (c : Code) (f : Nat) : Formula 2 :=
  .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ .var 1 ::ᵥ Term.numeral 0 ::ᵥ Term.numeral f ::ᵥ
      .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)

private def innerMatrix (pF : GorbowPRProgram.Program 1) (c : Code) (f fuel : Nat) : Formula 1 :=
  .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ Term.numeral fuel ::ᵥ Term.numeral 0 ::ᵥ
      Term.numeral f ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)

private theorem applyProvNumeral (pF : GorbowPRProgram.Program 1) (c : Code) (f : Nat) :
    applyProv pF c (Term.numeral f : Term 0) = .ex (.ex (outerMatrix pF c f)) := by
  simp only [applyProv, provability, substituteFormula, substituteCall, substNum,
    List.Vector.map_cons, List.Vector.map_nil]
  exact congrArg (fun t : Term 2 => Formula.ex (Formula.ex (Formula.equal
    (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (Term.numeral (Encodable.encode c) ::ᵥ Term.var 1 ::ᵥ Term.numeral 0 ::ᵥ t ::ᵥ
        Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)))) (liftTwoNumeral f)

private theorem instantiateOuter (pF : GorbowPRProgram.Program 1) (c : Code) (f fuel : Nat) :
    GorbowStandardInstances.instantiate (.ex (outerMatrix pF c f)) (Term.numeral fuel) =
      .ex (innerMatrix pF c f fuel) := by
  simp only [GorbowStandardInstances.instantiate, outerMatrix, substituteFormula, substituteCall,
    substNum, List.Vector.map_cons, List.Vector.map_nil]
  exact congrArg (fun t : Term 1 => Formula.ex (Formula.equal
    (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (Term.numeral (Encodable.encode c) ::ᵥ t ::ᵥ Term.numeral 0 ::ᵥ Term.numeral f ::ᵥ
        Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))) (liftNumeralSucc fuel)

private theorem instantiateInner (pF : GorbowPRProgram.Program 1) (c : Code) (f fuel cert : Nat) :
    GorbowStandardInstances.instantiate (innerMatrix pF c f fuel) (Term.numeral cert) =
      .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
        (GorbowPRNumeralCalculation.numeralArguments
          (GorbowEnumeratedProvability.arguments c fuel 0 f cert))) (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate, innerMatrix, substituteFormula, substituteCall,
    substNum, List.Vector.map_cons, List.Vector.map_nil]
  rfl

private theorem certificateDerivation (pF pR : GorbowPRProgram.Program 1)
    (q : GorbowPRProgram.Program 5) (c : Code) (hq : UniversalVerifier q) (f fuel cert : Nat)
    (hchk : GorbowEnumeratedProvability.check (c, fuel) 0 f cert = true) :
    Nonempty (Derivation (n := 0) (S pF pR q) (applyProv pF c (Term.numeral f))) := by
  obtain ⟨d⟩ := (GorbowNamedInternalProvability.Proof.numeralCertificates 5 pF pR q
    (GorbowEnumeratedProvability.arguments c fuel 0 f cert)).1
  have hv : GorbowPRProgram.evaluate q (GorbowEnumeratedProvability.arguments c fuel 0 f cert) = 1 := by
    simp [hq c fuel 0 f cert, hchk]
  rw [hv] at d
  have d1 : Derivation (GorbowNamedDefiningTheory.Theory (augmented pF q) pR)
      (GorbowStandardInstances.instantiate (innerMatrix pF c f fuel) (Term.numeral cert)) := by
    rw [instantiateInner]
    exact d
  obtain ⟨e1⟩ := existsIntroduction _ _ _ d1
  have e1' : Derivation (GorbowNamedDefiningTheory.Theory (augmented pF q) pR)
      (GorbowStandardInstances.instantiate (.ex (outerMatrix pF c f)) (Term.numeral fuel)) := by
    rw [instantiateOuter]
    exact e1
  obtain ⟨e2⟩ := existsIntroduction _ _ _ e1'
  have e3 : Derivation (n := 0) (GorbowNamedDefiningTheory.Theory (augmented pF q) pR)
      (applyProv pF c (Term.numeral f)) := by
    rw [applyProvNumeral]
    exact e2
  exact GorbowTheoryProofProof.monotonicity _ (S pF pR q) (namedToS pF pR q) 0 _ ⟨e3⟩

theorem sProofCertification : GorbowPublishedDCB.Targets.SProofCertification := by
  intro pF pR q c hA sigma hd
  obtain ⟨_, hq, hc⟩ := hA
  rw [← hc] at hd
  obtain ⟨fuel, cert, hchk⟩ := (GorbowEnumeratedProvability.Proof.exactNumericAcceptance c 0
    (GorbowSortedSyntaxCode.formulaCode sigma)).mpr ⟨sigma, rfl, hd⟩
  exact certificateDerivation pF pR q c hq _ fuel cert hchk

/-! ### Pr_D certificates by closed deduction -/

theorem dProofCertification : GorbowPublishedDCB.Targets.DProofCertification := by
  intro pF pR q c hA sigma hd
  obtain ⟨hdS⟩ := (GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) sigma).mp hd
  obtain ⟨hcert⟩ := sProofCertification pF pR q c hA (.imp (rho pF c) sigma) ⟨hdS⟩
  have hcal' := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  obtain ⟨hic⟩ := (GorbowSelectedDistribution.Proof.literalCodingCertificates
    (augmented pF q) pR hcal').2 (rho pF c) sigma
  obtain ⟨hicS⟩ := GorbowTheoryProofProof.monotonicity _ (S pF pR q) (sdToS pF pR q) 0 _ ⟨hic⟩
  have hic' : Derivation (S pF pR q) (.equal
      (GorbowBooleanTruth.binaryCodeTerm 0
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) sigma)))) := hicS
  obtain ⟨heq⟩ := GorbowTheoryEqualityProof.symmetry (S pF pR q) _ _ hic'
  have hr : Derivation (S pF pR q) (.imp (.equal
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) sigma)))
      (GorbowBooleanTruth.binaryCodeTerm 0
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))
      (.imp (GorbowStandardInstances.instantiate (provability pF c)
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) sigma))))
        (GorbowStandardInstances.instantiate (provability pF c)
          (GorbowBooleanTruth.binaryCodeTerm 0
            (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
            (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))))) :=
    .logical (.equalityReplace (provability pF c) _ _)
  rw [instantiateProv, instantiateProv] at hr
  exact GorbowTheoryProofProof.monotonicity (S pF pR q) (D pF pR q c) (fun _ h => Or.inl h) 0 _
    ⟨.mp (.mp hr heq) hcert⟩

/-! ### Selected reflection -/

/-- Context `[formula, agent, reflection-code]` of the printed template. -/
private def templateInner (pF : GorbowPRProgram.Program 1) (c : Code) : Formula 3 :=
  .imp (GorbowBooleanTruth.sentenceGuard (.var 0))
    (.imp (applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0 (.var 2) (.var 0)))
      (.knowledge (.var 1) (.var 0)))

private def rootDictionary (r : Nat) : Fin 1 → Term 0 := Fin.cases (Term.numeral r) Term.var

private def reflMiddle (pF : GorbowPRProgram.Program 1) (c : Code) (r : Nat) : Formula 2 :=
  substituteFormula (liftSubstitute (liftSubstitute (rootDictionary r))) (templateInner pF c)

private def reflBody (pF : GorbowPRProgram.Program 1) (c : Code) (r : Nat) : Formula 1 :=
  .imp (.agent (.var 0)) (.all (reflMiddle pF c r))

private def reflDictionary (r s : Nat) : Fin 3 → Term 1 :=
  Fin.cases (Term.numeral s) (Fin.cases (Term.var 0) (fun _ : Fin 1 => Term.numeral r))

private theorem reflDictionaryEq (r s : Nat) :
    (fun i : Fin 3 => GorbowSubstitution.substitute
      (Fin.cases (Term.numeral s) Term.var : Fin 2 → Term 1)
      (liftSubstitute (liftSubstitute (rootDictionary r)) i)) = reflDictionary r s := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ k =>
      cases k using Fin.cases with
      | zero =>
        show GorbowSubstitution.substitute (Fin.cases (Term.numeral s) Term.var : Fin 2 → Term 1)
          (GorbowSubstitution.substitute (fun i : Fin 1 => (Term.var i.succ : Term 2))
            (GorbowSubstitution.substitute (fun i : Fin 0 => (Term.var i.succ : Term 1))
              (Term.numeral r))) = Term.numeral r
        rw [substNum, substNum, substNum]
      | succ m => exact Fin.elim0 m

private theorem reflInstance (pF : GorbowPRProgram.Program 1) (c : Code) (r s : Nat) :
    GorbowStandardInstances.instantiate (reflMiddle pF c r) (Term.numeral s) =
      substituteFormula (reflDictionary r s) (templateInner pF c) := by
  unfold GorbowStandardInstances.instantiate reflMiddle
  rw [GorbowFormulaCompositionProof.composition, reflDictionaryEq]

private theorem reflProv (pF : GorbowPRProgram.Program 1) (c : Code) (r s : Nat) :
    substituteFormula (reflDictionary r s)
      (applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0 (.var 2) (.var 0) : Term 3)) =
      applyProv pF c
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1) := by
  unfold applyProv
  rw [GorbowFormulaCompositionProof.composition] <;> rfl

private theorem liftProv (pF : GorbowPRProgram.Program 1) (c : Code) (r s : Nat) :
    weakenClosed 1 (applyProv pF c
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 0)) =
      applyProv pF c
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1) := by
  unfold weakenClosed applyProv
  rw [GorbowFormulaCompositionProof.composition]
  exact congrArg (fun σ : Fin 1 → Term 1 => substituteFormula σ (provability pF c))
    (funext fun _ => liftBin r s)

/-- Reflection in any theory with the instantiated template, the literal
sentence guard and the closed Pr_D premise as closed axioms; the agent is
free in context one and generalized at the end. -/
private theorem reflectionCore (T : Sentence → Prop) (pF : GorbowPRProgram.Program 1) (c : Code)
    (A : Selector) (r s : Nat)
    (hR : T (GorbowStandardInstances.instantiate (reflectionTemplate pF c) (Term.numeral r)))
    (hG : T (GorbowBooleanTruth.sentenceGuard (Term.numeral s)))
    (hP : T (applyProv pF c
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s)))) :
    Nonempty (Derivation T (everyone A s)) := by
  obtain ⟨dR⟩ := openInstance (T := T) (reflBody pF c r) (Derivation.axiom (n := 1) _ hR)
  have gS : Derivation T (GorbowBooleanTruth.sentenceGuard (Term.numeral s : Term 1)) := by
    have h := Derivation.axiom (A := T) (n := 1) _ hG
    rw [liftGuard] at h
    exact h
  have pS : Derivation T (applyProv pF c
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1)) := by
    have h := Derivation.axiom (A := T) (n := 1) _ hP
    rw [liftProv] at h
    exact h
  have i2 : Derivation T (.imp (.all (reflMiddle pF c r))
      (substituteFormula (reflDictionary r s) (templateInner pF c))) := by
    rw [← reflInstance pF c r s]
    exact .logical (.allInstantiate (reflMiddle pF c r) (Term.numeral s))
  have i3 : Derivation T (.imp (.all (reflMiddle pF c r))
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral s : Term 1))
        (.imp (substituteFormula (reflDictionary r s)
          (applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0 (.var 2) (.var 0) : Term 3)))
          (.knowledge (.var 0) (Term.numeral s))))) := i2
  rw [reflProv] at i3
  have h1 : Derivation T (.imp (.agent (.var 0))
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral s : Term 1))
        (.imp (applyProv pF c
          (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1))
          (.knowledge (.var 0) (Term.numeral s))))) :=
    compose i3 dR
  have h2 : Derivation T (.imp (.agent (.var 0))
      (.imp (applyProv pF c
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s) : Term 1))
        (.knowledge (.var 0) (Term.numeral s)))) :=
    mpUnder h1 (liftK _ gS)
  have h3 : Derivation T (.imp (.agent (.var 0)) (.knowledge (.var 0) (Term.numeral s))) :=
    mpUnder h2 (liftK _ pS)
  have h4 : Derivation T (.imp (.agent (.var 0))
      (.imp A.val (.knowledge (.var 0) (Term.numeral s)))) :=
    weakenUnder A.val h3
  exact ⟨.generalize h4⟩

theorem selectedReflection : GorbowPublishedDCB.Targets.SelectedReflection := by
  intro pF pR q c hA A sigma
  have hcal' := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  obtain ⟨hbicS⟩ := publishedDiagonal pF pR q c hA.1
  obtain ⟨hbic⟩ := GorbowTheoryProofProof.monotonicity (S pF pR q) (D pF pR q c)
    (fun _ h => Or.inl h) 0 _ ⟨hbicS⟩
  have hrho : Derivation (D pF pR q c) (rho pF c) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
      (Derivation.axiom (A := D pF pR q c) (n := 0) (rho pF c) (Or.inr rfl))
  have himp : Derivation (D pF pR q c) (.imp (rho pF c)
      (GorbowStandardInstances.instantiate (reflectionTemplate pF c)
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))))) :=
    .mp (.logical (.andLeft _ _)) hbic
  have hRd := Derivation.mp himp hrho
  obtain ⟨hgSD⟩ := (GorbowSelectedDistribution.Proof.literalCodingCertificates
    (augmented pF q) pR hcal').1 sigma
  obtain ⟨hg⟩ := GorbowTheoryProofProof.monotonicity _ (D pF pR q c)
    (fun σ h => Or.inl (sdToS pF pR q σ h)) 0 _ ⟨hgSD⟩
  have hg' : Derivation (D pF pR q c)
      (GorbowBooleanTruth.sentenceGuard
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))) := hg
  have core := reflectionCore
    (GorbowClosedDeduction.extend (GorbowClosedDeduction.extend
      (GorbowClosedDeduction.extend (D pF pR q c)
        (GorbowStandardInstances.instantiate (reflectionTemplate pF c)
          (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))))
        (GorbowBooleanTruth.sentenceGuard
          (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))
      (applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))))
    pF c A (GorbowSortedSyntaxCode.formulaCode (rho pF c))
    (GorbowSortedSyntaxCode.formulaCode sigma)
    (Or.inl (Or.inl (Or.inr rfl))) (Or.inl (Or.inr rfl)) (Or.inr rfl)
  obtain ⟨c0⟩ := dischargeOne (dischargeOne (dischargeOne core))
  exact ⟨.mp (.mp c0 hRd) hg'⟩

/-! ### Selected distribution and the three clauses -/

theorem selectedDistribution : GorbowPublishedDCB.Targets.SelectedDistribution := by
  intro pF pR q c hA A sigma tau
  have hcal' := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  obtain ⟨h⟩ := GorbowSelectedDistribution.Proof.selectedAgentClosure (augmented pF q) pR hcal'
    A sigma tau
  exact GorbowTheoryProofProof.monotonicity _ (D pF pR q c)
    (fun σ hσ => Or.inl (sdToS pF pR q σ hσ)) 0 _ ⟨h⟩

theorem completeThree : GorbowPublishedDCB.Targets.CompleteThree := by
  obtain ⟨pF, pR, q, c, hA⟩ := actualParameters
  refine ⟨pF, pR, q, c, hA, fun A sigma tau => ⟨fun hd => ?_,
    selectedDistribution pF pR q c hA A sigma tau, selectedReflection pF pR q c hA A sigma⟩⟩
  obtain ⟨p1⟩ := dProofCertification pF pR q c hA sigma hd
  obtain ⟨p2⟩ := selectedReflection pF pR q c hA A sigma
  exact ⟨.mp p2 p1⟩

theorem fullTarget : GorbowPublishedDCB.Targets.Target :=
  ⟨finiteSPresentation, actualParameters, publishedDiagonal, provabilityCalibration,
    sProofCertification, dProofCertification, selectedReflection, selectedDistribution,
    completeThree⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.Proof
