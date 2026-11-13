module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraphEquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open GorbowPRDefiningEquations GorbowFormulaSubstitution GorbowSubstitution List.Vector
open NamedArithmeticGraph

private theorem substNumeral {m n : Nat} (sigma : Fin m → Term n) (k : Nat) :
    substitute sigma (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n sigma k

private theorem substCall {m n arity : Nat} (sigma : Fin m → Term n)
    (tag : Nat) (args : List.Vector (Term m) arity) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution m n arity tag args sigma

private theorem vectorTwo {alpha : Type} (f : Fin 2 → alpha) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

private theorem gateValue (k x : Nat) :
    evaluate SymbolicVerifier.gate (k ::ᵥ x ::ᵥ nil) = if k = 0 then 0 else x := by
  cases k <;> rfl

private theorem verifierValue (q0 : Program 5) (v : List.Vector Nat 5) :
    evaluate (SymbolicVerifier.verifier q0) v =
      if v.get (4 : Fin 5) = 0 then 0 else evaluate q0 v := by
  change evaluate SymbolicVerifier.gate
    (List.Vector.ofFn fun i => evaluate (SymbolicVerifier.arguments q0 i) v) = _
  rw [vectorTwo]
  exact gateValue _ _

private theorem emptyCheck (c : Code) (fuel n formula : Nat) :
    GorbowEnumeratedProvability.check (c,fuel) n formula 0 = false := by
  have he : GorbowNumericCertificate.decodeCertificate 0 = some [] :=
    (GorbowNumericCertificateProof.exactDecoding.2 0 []).mpr rfl
  cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula <;>
    simp [GorbowEnumeratedProvability.check, GorbowTheoryNumericCertificate.check, hf, he,
      GorbowTheoryChecker.verifies, GorbowTheoryChecker.checkProof,
      GorbowTheoryChecker.run]

theorem sameNumericChecker : SymbolicVerifierTargets.SameNumericChecker := by
  intro q0 hq0 c fuel n formula cert
  rw [verifierValue]
  have hcert : (GorbowEnumeratedProvability.arguments c fuel n formula cert).get
      (4 : Fin 5) = cert := rfl
  rw [hcert]
  by_cases hz : cert = 0
  · subst cert
    rw [if_pos rfl, emptyCheck]
    rfl
  · rw [if_neg hz, hq0 c fuel n formula cert]

private def equalityTransitivity {T : Sentence → Prop} {ctx : Nat}
    (s t u : Term ctx) (hst : Derivation T (.equal s t)) (htu : Derivation T (.equal t u)) :
    Derivation T (.equal s u) := by
  have h := Derivation.logical (A := T)
    (.equalityReplace (.equal (renameTerm Fin.succ s) (.var 0)) t u)
  change Derivation T (.imp (.equal t u)
    (.imp (.equal (substitute (Fin.cases t Term.var) (renameTerm Fin.succ s)) t)
      (.equal (substitute (Fin.cases u Term.var) (renameTerm Fin.succ s)) u))) at h
  rw [Support.shiftCancel, Support.shiftCancel] at h
  exact .mp (.mp h htu) hst

private def termCongruence {T : Sentence → Prop} {ctx : Nat}
    (f : Term (ctx+1)) (s t : Term ctx) (h : Derivation T (.equal s t)) :
    Derivation T (.equal (substitute (Fin.cases s Term.var) f)
      (substitute (Fin.cases t Term.var) f)) := by
  let fs := substitute (Fin.cases s Term.var) f
  let phi := Formula.equal (renameTerm Fin.succ fs) f
  have hi : Derivation T (GorbowStandardInstances.instantiate phi s) := by
    change Derivation T (.equal
      (substitute (Fin.cases s Term.var) (renameTerm Fin.succ fs)) fs)
    rw [Support.shiftCancel]
    exact .logical (.reflexive fs)
  have hr : Derivation T (GorbowStandardInstances.instantiate phi t) :=
    .mp (.mp (.logical (.equalityReplace phi s t)) h) hi
  change Derivation T (.equal
    (substitute (Fin.cases t Term.var) (renameTerm Fin.succ fs))
    (substitute (Fin.cases t Term.var) f)) at hr
  rw [Support.shiftCancel] at hr
  exact hr

private def firstArgument {ctx : Nat} (tag : Nat) (y : Term ctx) : Term (ctx+1) :=
  call tag (.var 0 ::ᵥ renameTerm Fin.succ y ::ᵥ nil)

private theorem firstArgumentAt {ctx : Nat} (tag : Nat) (y t : Term ctx) :
    substitute (Fin.cases t Term.var) (firstArgument tag y) = call tag (t ::ᵥ y ::ᵥ nil) := by
  simp only [firstArgument, substCall, List.Vector.map_cons, List.Vector.map_nil,
    substitute, Fin.cases_zero, Support.shiftCancel]

theorem openEmptyCertificate : SymbolicVerifierTargets.OpenEmptyCertificate := by
  intro n p tag q0 htag ctx index fuel context formula
  let q := SymbolicVerifier.verifier q0
  let inp := SymbolicVerifier.input index fuel context formula (Term.zero : Term ctx)
  let gs := SymbolicVerifier.arguments q0
  let y := call (tag+6) inp
  have ha0 : GorbowPRChildTags.argumentTag SymbolicVerifier.gate gs (0 : Fin 2) = 5 := rfl
  have ha1 : GorbowPRChildTags.argumentTag SymbolicVerifier.gate gs (1 : Fin 2) = 6 := rfl
  have hg : (nodes p)[tag+1]? = some ⟨2,SymbolicVerifier.gate⟩ :=
    GorbowPRSubtree.Proof.lookupTransport n p tag ⟨5,q⟩ 1 ⟨2,SymbolicVerifier.gate⟩ htag
      (GorbowPRChildTags.Proof.compositionFunction 5 2 SymbolicVerifier.gate gs)
  have hb0 := GorbowPRSubtree.Proof.lookupTransport n p (tag+1)
    ⟨2,SymbolicVerifier.gate⟩ 1 ⟨1,GorbowNamedInternalProvability.zeroUnary⟩ hg
      (GorbowPRChildTags.Proof.recursionBase 1 GorbowNamedInternalProvability.zeroUnary
        (.projection (2 : Fin 3)))
  have hb : (nodes p)[tag+2]? = some ⟨1,GorbowNamedInternalProvability.zeroUnary⟩ := by
    simpa only [Nat.add_assoc] using hb0
  have hz0 := GorbowPRSubtree.Proof.lookupTransport n p (tag+2)
    ⟨1,GorbowNamedInternalProvability.zeroUnary⟩ 1 ⟨0,Program.zero⟩ hb
      (GorbowPRChildTags.Proof.compositionFunction 1 0 Program.zero Fin.elim0)
  have hz : (nodes p)[tag+3]? = some ⟨0,Program.zero⟩ := by
    simpa only [Nat.add_assoc] using hz0
  have hp0 := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨5,q⟩
    (GorbowPRChildTags.argumentTag SymbolicVerifier.gate gs 0)
    ⟨5,Program.projection (4 : Fin 5)⟩ htag
      (GorbowPRChildTags.Proof.compositionArgument 5 2 SymbolicVerifier.gate gs 0)
  have hp : (nodes p)[tag+5]? = some ⟨5,Program.projection (4 : Fin 5)⟩ := by
    simpa only [ha0] using hp0
  obtain ⟨hc⟩ := Support.intoRegistry p q tag htag _
    (Equations.composition SymbolicVerifier.gate gs tag ctx inp)
  have hv : (List.Vector.ofFn fun i => call
      (tag + GorbowPRChildTags.argumentTag SymbolicVerifier.gate gs i) inp) =
      call (tag+5) inp ::ᵥ y ::ᵥ nil := by
    rw [vectorTwo]
    rfl
  rw [hv] at hc
  obtain ⟨hproj⟩ := Support.intoRegistry p (Program.projection (4 : Fin 5)) (tag+5) hp _
    (Equations.projection (4 : Fin 5) (tag+5) ctx inp)
  have hproj' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+5) inp) .zero) := hproj
  have hcong := termCongruence (firstArgument (tag+1) y)
    (call (tag+5) inp) .zero hproj'
  rw [firstArgumentAt,firstArgumentAt] at hcong
  obtain ⟨hbase⟩ := Support.intoRegistry p SymbolicVerifier.gate (tag+1) hg _
    (Equations.recursionZero GorbowNamedInternalProvability.zeroUnary
      (.projection (2 : Fin 3)) (tag+1) ctx (y ::ᵥ nil))
  obtain ⟨hzeroUnary⟩ := Support.intoRegistry p GorbowNamedInternalProvability.zeroUnary
    (tag+2) hb _ (Equations.composition Program.zero Fin.elim0 (tag+2) ctx (y ::ᵥ nil))
  have hempty : (List.Vector.ofFn fun i : Fin 0 => call
      ((tag+2) + GorbowPRChildTags.argumentTag Program.zero
        (Fin.elim0 : Fin 0 → Program 1) i) (y ::ᵥ nil)) =
      (nil : List.Vector (Term ctx) 0) := by
    apply List.Vector.ext
    intro i
    exact Fin.elim0 i
  rw [hempty] at hzeroUnary
  obtain ⟨hzero⟩ := Support.intoRegistry p Program.zero (tag+3) hz _
    (Equations.zero (tag+3) ctx)
  have hbase' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+1) (.zero ::ᵥ y ::ᵥ nil)) (call (tag+2) (y ::ᵥ nil))) := by
    simpa only [Nat.add_assoc] using hbase
  have hzeroUnary' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+2) (y ::ᵥ nil)) (call (tag+3) nil)) := by
    simpa only [Nat.add_assoc] using hzeroUnary
  exact ⟨equalityTransitivity _ _ _ hc
    (equalityTransitivity _ _ _ hcong
      (equalityTransitivity _ _ _ hbase' (equalityTransitivity _ _ _ hzeroUnary' hzero)))⟩

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
    (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
      (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
    Nonempty (Derivation (S pF pR q) phi) :=
  GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

private theorem sourceEmptyOpen (pF pR : Program 1) (q0 : Program 5) (ctx : Nat)
    (index fuel context formula : Term ctx) :
    Nonempty (Derivation (S pF pR (SymbolicVerifier.verifier q0))
      (.equal (call (GorbowNamedInternalProvability.checkerTag pF)
        (SymbolicVerifier.input index fuel context formula .zero)) .zero)) :=
  inSource pF pR (SymbolicVerifier.verifier q0) _
    (openEmptyCertificate 4 _ (GorbowNamedInternalProvability.checkerTag pF) q0
      (GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR
        (SymbolicVerifier.verifier q0)) ctx index fuel context formula)

private def successTemplate {ctx : Nat} (tag : Nat)
    (index fuel context formula : Term ctx) : Formula (ctx+1) :=
  .equal (call tag (SymbolicVerifier.input (renameTerm Fin.succ index)
    (renameTerm Fin.succ fuel) (renameTerm Fin.succ context)
    (renameTerm Fin.succ formula) (.var 0))) (Term.numeral 1)

private theorem successTemplateAt {ctx : Nat} (tag : Nat)
    (index fuel context formula cert : Term ctx) :
    GorbowStandardInstances.instantiate (successTemplate tag index fuel context formula) cert =
      .equal (call tag (SymbolicVerifier.input index fuel context formula cert))
        (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate, successTemplate, SymbolicVerifier.input,
    substituteFormula, substCall,
    List.Vector.map_cons,List.Vector.map_nil,Support.shiftCancel,substitute,
    Fin.cases_zero, substNumeral]

private theorem sourceNonemptyOpen (pF pR : Program 1) (q0 : Program 5) (c : Code) :
    Nonempty (Derivation (S pF pR (SymbolicVerifier.verifier q0))
      (n := 3) (.imp (.equal (call (GorbowNamedInternalProvability.checkerTag pF)
        (SymbolicVerifier.input (Term.numeral (Encodable.encode c)) (.var 2) .zero (.var 1) (.var 0)))
        (Term.numeral 1)) (.neg (.equal (.var 0) .zero)))) := by
  let T := S pF pR (SymbolicVerifier.verifier q0)
  let tag := GorbowNamedInternalProvability.checkerTag pF
  let index : Term 3 := Term.numeral (Encodable.encode c)
  let empty := call tag (SymbolicVerifier.input index (.var 2) .zero (.var 1) .zero)
  let P : Formula 3 := .equal (call tag
    (SymbolicVerifier.input index (.var 2) .zero (.var 1) (.var 0))) (Term.numeral 1)
  let E : Formula 3 := .equal (.var 0) .zero
  let B : Formula 3 := .equal .zero (Term.numeral 1)
  obtain ⟨hzero⟩ := sourceEmptyOpen pF pR q0 3 index (.var 2) .zero (.var 1)
  have hreplace : Derivation T (.imp E (.imp P (.equal empty (Term.numeral 1)))) := by
    have h := Derivation.logical (A := T)
      (.equalityReplace (successTemplate tag index (.var 2) .zero (.var 1)) (.var 0) .zero)
    rw [GorbowPACore.logicalFormula, successTemplateAt, successTemplateAt] at h
    exact h
  have htoBad : Derivation T (.imp (.equal empty (Term.numeral 1)) B) := by
    have h := Derivation.logical (A := T)
      (.equalityReplace (.equal (.var 0) (Term.numeral 1) : Formula 4) empty .zero)
    have h' : Derivation T (.imp (.equal empty .zero)
        (.imp (.equal empty (Term.numeral 1)) B)) := by
      simpa only [GorbowPACore.logicalFormula, GorbowStandardInstances.instantiate,
        substituteFormula, substitute, Fin.cases_zero, substNumeral] using h
    exact .mp h' hzero
  obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
  obtain ⟨hn3⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ ⟨hn⟩ 3
  have hnotBad : Derivation T (.neg B) := by
    simpa only [weakenClosed, substituteFormula, substNumeral, B, Term.numeral] using hn3
  have he : Hilbert.Local T 3 [.neg (.neg E),P] E :=
    .mp (.base (Hilbert.doubleNegation E)) (.hypothesis List.mem_cons_self)
  have hp : Hilbert.Local T 3 [.neg (.neg E),P] P :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hb : Hilbert.Local T 3 [.neg (.neg E),P] B :=
    .mp (.base htoBad) (.mp (.mp (.base hreplace) he) hp)
  have hne : Hilbert.Local T 3 [P] (.neg E) := Hilbert.Local.classical (.neg E)
    (Hilbert.Local.explosion (.neg E) hb (.base hnotBad))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hne)⟩

theorem sameSourceSymbolicNonempty : SymbolicVerifierTargets.SameSourceSymbolicNonempty := by
  obtain ⟨q0,hq0⟩ := GorbowEnumeratedProvability.Proof.fixedUniversalProgram
  let q := SymbolicVerifier.verifier q0
  have hq : UniversalVerifier q := sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstall,hFixed,hGInstall⟩ :=
    InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK pG
  refine ⟨q0,pF,pR,c,tagCK,pCK,tagG,pG,hq0,hA,hSyntax,hCK,hInstall,hFixed,hG,hGInstall,?_,?_⟩
  · obtain ⟨h⟩ := sourceEmptyOpen pF pR q0 4 (.var 3) (.var 2) (.var 1) (.var 0)
    exact ⟨.generalize (.generalize (.generalize (.generalize h)))⟩
  · obtain ⟨h⟩ := sourceNonemptyOpen pF pR q0 c
    exact ⟨.generalize (.generalize (.generalize h))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierProof
