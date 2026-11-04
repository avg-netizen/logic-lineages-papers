module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruthTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowNameDictionaryProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemanticsProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof

@[expose] public section
/-! Actual L-minus atomic FS on the real published-D ground. The source 1,1
evaluator and 3,1 substitution headers are reduced through the actual named
dispatcher, the diagonal fallback and the calibrated atomic source programs;
the guard is the derived arithmetic-term relation law. Ground-independent
syntactic dictionaries are reproved here, and the atomic schemas are paid at
every positive revision via same-ground fixedMinus and the exact revision image.
No whole-ground identity, stagezero or source12 promotion is claimed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowPublishedModel GorbowStandardInstances GorbowSortedSyntaxCode GorbowRegistryTuple
open GorbowAtomicParameters GorbowAtomicTruth GorbowRevisionComposition GorbowFormulaSubstitution

attribute [local irreducible] GorbowRegistryTuple.header

/-! ### Actual source headers -/

private theorem evalHeader (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (t : Term 0) (ht : ArithmeticTerm t) :
    ∀ I, (ground pF pR q).universalFunction (header 1 1 [termCode t]) =
      t.realize I Fin.elim0 := by
  intro I
  have h1 : (ground pF pR q).universalFunction (header 1 1 [termCode t]) =
      GorbowSourceRegistryPadding.sourceFunction (header 1 1 [termCode t]) :=
    GorbowPublishedQuantifierTruth.Proof.namedFunctions pF pR q c hA (1, 1)
      (by simp [GorbowSourceRegistryPadding.functionNames]) [termCode t] rfl
  have h2 : GorbowSourceRegistryPadding.sourceFunction (header 1 1 [termCode t]) =
      GorbowAtomicRegistry.functionProgram (header 1 1 [termCode t]) :=
    GorbowDiagonalRegistryProof.fallback.2 1 1 [termCode t] (by simp)
  exact h1.trans (h2.trans (GorbowAtomicRegistryProof.actualCalibration.1 t ht I))

private theorem substHeader (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (m : Nat) (R : Formula m) (sigma : Fin m → Term 0) :
    (ground pF pR q).universalFunction
        (header 3 1 [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))]) =
      formulaCode (substituteFormula sigma R) := by
  have h1 : (ground pF pR q).universalFunction
        (header 3 1 [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))]) =
      GorbowSourceRegistryPadding.sourceFunction
        (header 3 1 [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))]) :=
    GorbowPublishedQuantifierTruth.Proof.namedFunctions pF pR q c hA (3, 1)
      (by simp [GorbowSourceRegistryPadding.functionNames])
      [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))] rfl
  have h2 : GorbowSourceRegistryPadding.sourceFunction
        (header 3 1 [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))]) =
      GorbowAtomicRegistry.functionProgram
        (header 3 1 [m, formulaCode R, tuple (List.ofFn (fun i => termCode (sigma i)))]) :=
    GorbowDiagonalRegistryProof.fallback.2 3 1 _ (by simp)
  exact h1.trans (h2.trans (GorbowAtomicRegistryProof.actualCalibration.2 m R sigma))

theorem headerCalibration : GorbowPublishedAtomicTruth.Targets.HeaderCalibration := by
  intro pF pR q c hA
  exact ⟨fun t ht I => evalHeader pF pR q c hA t ht I,
    fun m R sigma => substHeader pF pR q c hA m R sigma⟩

/-! ### Guard, closure and evaluation on the actual ground -/

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ = header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as

private theorem actualGuard (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) {n : Nat} (t : Term n) (P : Nat → Prop) (ρ : Fin n → Nat) :
    (GorbowSortedQuantifierTruth.arithmeticTermGuard t).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ ↔
      GorbowSortedBooleanCode.arithmeticTermCode
        (t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ) = true := by
  change (ground pF pR q).universalRelation ((headerTerm 1 2 [t]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons, List.map_nil]
  exact ((GorbowPublishedQuantifierTruth.Proof.sourceDispatch pF pR q c hA).1
    (t.realize _ ρ) 0).2.2.1

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem actualClosure (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (n : Nat) : ∀ (φ : Formula n) (P : Nat → Prop),
    (arithmeticClosure φ).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 ↔
      ∀ ρ : Fin n → Nat, (∀ i, GorbowSortedBooleanCode.arithmeticTermCode (ρ i) = true) →
        φ.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ := by
  induction n with
  | zero =>
    intro φ P
    constructor
    · intro h ρ _
      have he : ρ = Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [he]; exact h
    · intro h; exact h Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    intro φ P
    change (arithmeticClosure (Formula.all
      (.imp (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0)) φ))).realize _ _ ↔ _
    rw [ih]
    constructor
    · intro h ρ hρ
      have he : Fin.cases (ρ 0) (fun i : Fin n => ρ i.succ) = ρ := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      have hv := h (fun i : Fin n => ρ i.succ) (fun i => hρ i.succ) (ρ 0)
      have hg : (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0)).realize
          (GorbowRevisionSemantics.interpretation (ground pF pR q) P)
          (Fin.cases (ρ 0) (fun i : Fin n => ρ i.succ)) :=
        (actualGuard pF pR q c hA (n := n+1) (.var 0) P _).mpr (hρ 0)
      have hx := hv hg
      rw [he] at hx
      exact hx
    · intro h ρ hρ x hx
      apply h (Fin.cases x ρ)
      intro i
      refine Fin.cases ?_ (fun j => hρ j) i
      exact (actualGuard pF pR q c hA (n := n+1) (.var 0) P (Fin.cases x ρ)).mp hx

private theorem actualEvaluation (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) {n : Nat} (t : Term n) (P : Nat → Prop) (ρ : Fin n → Nat)
    (s : Term 0) (hs : ArithmeticTerm s)
    (ht : t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ = termCode s) :
    (evaluationTerm t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ =
      s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  change (ground pF pR q).universalFunction ((headerTerm 1 1 [t]).realize _ ρ) = _
  rw [headerRealize]
  simp only [List.map_cons, List.map_nil, ht]
  exact evalHeader pF pR q c hA s hs _

/-! ### Small syntactic dictionaries -/

private theorem namesIndex {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names)
    (j : Fin n) : (GorbowNameDictionary.namesList names).idxOf (names j).val = j.val := by
  have hi : Function.Injective (fun j => (names j).val) := Fin.val_injective.comp hn
  have hl : (GorbowNameDictionary.namesList names).Nodup := List.nodup_ofFn.mpr hi
  have he := hl.idxOf_getElem j.val (by simp [GorbowNameDictionary.namesList, j.isLt])
  simpa [GorbowNameDictionary.namesList] using he

private theorem codeLookup {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names)
    (j : Fin n) : codeDictionary names (names j) = .var j := by
  simp [codeDictionary, namesIndex names hn j, List.getD_eq_getElem?_getD, j.isLt]

private theorem codeUnused {n m : Nat} (names : Fin n → Fin m) (i : Fin m)
    (hi : ¬∃ j, names j = i) : codeDictionary names i = Term.numeral (termCode (.zero : Term 0)) := by
  have hm : i.val ∉ GorbowNameDictionary.namesList names := by
    simp only [GorbowNameDictionary.namesList, List.mem_ofFn]
    rintro ⟨j, hj⟩; exact hi ⟨j, Fin.ext hj⟩
  have hh := List.idxOf_eq_length_iff.mpr hm
  unfold codeDictionary
  rw [hh]
  simp [GorbowNameDictionary.namesList, List.getD_eq_getElem?_getD]

private theorem codeEntries {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names)
    (ts : Fin n → Term 0) (I : Interpretation) (ρ : Fin n → Nat)
    (hρ : ∀ j, ρ j = termCode (ts j)) (i : Fin m) :
    (codeDictionary names i).realize I ρ = termCode (GorbowNameDictionary.dictionary names ts i) := by
  by_cases hi : ∃ j, names j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [codeLookup names hn j, GorbowNameDictionaryProof.lookup n m 0 names hn ts j]
    exact hρ j
  · rw [codeUnused names i hi, GorbowNameDictionaryProof.unusedZero n m 0 names ts i hi]
    exact numeral_realize _ _ _

private theorem valueEntries (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names)
    (ts : Fin n → Term 0) (hts : ∀ j, ArithmeticTerm (ts j)) (P : Nat → Prop)
    (ρ : Fin n → Nat) (hρ : ∀ j, ρ j = termCode (ts j)) (i : Fin m) :
    (valueDictionary names i).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ =
      (GorbowNameDictionary.dictionary names ts i).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  by_cases hi : ∃ j, names j = i
  · obtain ⟨j, rfl⟩ := hi
    change (GorbowNameDictionary.dictionary names (fun j => evaluationTerm (.var j)) (names j)).realize _ _ = _
    rw [GorbowNameDictionaryProof.lookup n m n names hn _ j,
      GorbowNameDictionaryProof.lookup n m 0 names hn ts j]
    exact actualEvaluation pF pR q c hA (Term.var j) P ρ (ts j) (hts j) (hρ j)
  · change (GorbowNameDictionary.dictionary names (fun j => evaluationTerm (.var j)) i).realize _ _ = _
    rw [GorbowNameDictionaryProof.unusedZero n m n names _ i hi,
      GorbowNameDictionaryProof.unusedZero n m 0 names ts i hi]
    rfl

private theorem tupleValue {n m : Nat} (names : Fin n → Fin m) (hn : Function.Injective names)
    (ts : Fin n → Term 0) (I : Interpretation) (ρ : Fin n → Nat)
    (hρ : ∀ j, ρ j = termCode (ts j)) :
    (argumentTuple names).realize I ρ =
      tuple (List.ofFn (fun i => termCode (GorbowNameDictionary.dictionary names ts i))) := by
  rw [argumentTuple, (GorbowRegistryTupleProof.termCalibration n I ρ).2.1]
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  exact codeEntries names hn ts I ρ hρ i

/-! ### Exact instance codes -/

theorem codeCalibration : GorbowPublishedAtomicTruth.Targets.CodeCalibration := by
  intro pF pR q c hA n m R names hn ts hts P ρ hρ
  have ht := tupleValue names hn ts (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ hρ
  change (ground pF pR q).universalFunction
    ((headerTerm 3 1 [Term.numeral m, formulaQuote n R, argumentTuple names]).realize _ ρ) = _
  rw [(GorbowRegistryTupleProof.termCalibration n
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) ρ).2.2]
  simp only [List.map_cons, List.map_nil, formulaQuote, numeral_realize, ht]
  exact substHeader pF pR q c hA m R (GorbowNameDictionary.dictionary names ts)

/-! ### Atomic schemas at actual positive revisions -/

private theorem bodyRealization {n m : Nat} (R : Formula m) (names : Fin n → Fin m)
    (g : GorbowRevisionSemantics.Ground) P ρ :
    (atomicBody R names).realize (GorbowRevisionSemantics.interpretation g P) ρ ↔
      (P ((instanceCodeTerm R names).realize (GorbowRevisionSemantics.interpretation g P) ρ) ↔
        (substituteFormula (valueDictionary names) R).realize
          (GorbowRevisionSemantics.interpretation g P) ρ) := by
  simp only [atomicBody, GorbowBooleanTruth.biconditional, Formula.realize,
    GorbowRevisionSemantics.interpretation, iff_def]

private theorem atomicMinus {m : Nat} {R : Formula m} (hr : AtomicMinus R) :
    GorbowRevisionSemantics.MinusFormula R := by
  cases R <;> simp_all [AtomicMinus, GorbowRevisionSemantics.MinusFormula]

private theorem schemaAt (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) {n m : Nat} (R : Formula m) (names : Fin n → Fin m)
    (hr : AtomicMinus R) (hn : Function.Injective names) (initial : Nat → Prop) (k : Nat) :
    (atomicAxiom R names).realize
      (GorbowSortedRevision.stage (ground pF pR q) initial (k+1)) Fin.elim0 := by
  change (arithmeticClosure (atomicBody R names)).realize
    (GorbowRevisionSemantics.interpretation (ground pF pR q)
      (GorbowSortedRevision.extensions (ground pF pR q) initial (k+1))) Fin.elim0
  apply (actualClosure pF pR q c hA n (atomicBody R names) _).mpr
  intro ρ hρ
  have hex : ∀ j : Fin n, ∃ t : Term 0, ρ j = termCode t ∧ ArithmeticTerm t := by
    intro j
    exact (GorbowSortedBooleanCodeProof.exactDomains.2.2 (ρ j)).mp (hρ j)
  choose ts hcodes hts using hex
  apply (bodyRealization R names (ground pF pR q) _ ρ).mpr
  rw [GorbowPublishedAtomicTruth.Proof.codeCalibration pF pR q c hA n m R names hn ts hts _ ρ hcodes]
  let σ := GorbowNameDictionary.dictionary names ts
  have hs := substituteFormula_realize R
    (GorbowSortedRevision.stage (ground pF pR q) initial k) Fin.elim0 σ
  have hm := (GorbowRevisionSemanticsProof.fixedMinus (ground pF pR q)
      (GorbowSortedRevision.extensions (ground pF pR q) initial k)
      (GorbowSortedRevision.extensions (ground pF pR q) initial (k+1))).2
    m R (fun i => (σ i).realize (GorbowSortedRevision.stage (ground pF pR q) initial k) Fin.elim0)
    (atomicMinus hr)
  have hv := valueEntries pF pR q c hA names hn ts hts
    (GorbowSortedRevision.extensions (ground pF pR q) initial (k+1)) ρ hcodes
  have he : (fun i => (σ i).realize (GorbowSortedRevision.stage (ground pF pR q) initial k) Fin.elim0) =
      (fun i => (valueDictionary names i).realize
        (GorbowSortedRevision.stage (ground pF pR q) initial (k+1)) ρ) := by
    funext i
    exact ((GorbowRevisionSemanticsProof.fixedMinus (ground pF pR q)
      (GorbowSortedRevision.extensions (ground pF pR q) initial k)
      (GorbowSortedRevision.extensions (ground pF pR q) initial (k+1))).1
      0 (σ i) Fin.elim0).trans (hv i).symm
  have hright := substituteFormula_realize R
    (GorbowSortedRevision.stage (ground pF pR q) initial (k+1)) ρ (valueDictionary names)
  have hlast : R.realize (GorbowSortedRevision.stage (ground pF pR q) initial (k+1))
      (fun i => (σ i).realize (GorbowSortedRevision.stage (ground pF pR q) initial k) Fin.elim0) ↔
      (substituteFormula (valueDictionary names) R).realize
        (GorbowSortedRevision.stage (ground pF pR q) initial (k+1)) ρ := by
    rw [he]
    exact hright.symm
  exact ((GorbowSortedRevisionProof.exactImage (ground pF pR q)
    (GorbowSortedRevision.extensions (ground pF pR q) initial k)).1 (substituteFormula σ R)).trans
      (hs.trans (hm.trans hlast))

theorem positiveAtomicSchemas : GorbowPublishedAtomicTruth.Targets.PositiveAtomicSchemas := by
  intro pF pR q c hA n m R names hr hn _ k
  exact schemaAt pF pR q c hA R names hr hn (theoremCodes pF pR q c) k

theorem fullTarget : GorbowPublishedAtomicTruth.Targets.Target :=
  ⟨headerCalibration, codeCalibration, positiveAtomicSchemas⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.Proof
