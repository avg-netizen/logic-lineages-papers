module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralTagTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
/-! Effective families of ORIGINAL syntax and ORIGINAL proof certificates.
The family parameter is external data, not an added object-language rule. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
open GorbowSyntax GorbowTheoryProof GorbowPACore GorbowFormulaSubstitution
open GorbowSortedSyntaxCode GorbowTheoryCertificateOperations

variable {alpha : Type} [Primcodable alpha]

def TermEffective {n : Nat} (t : alpha → Term n) : Prop :=
  Primrec (fun x => GorbowTermPrefixCode.encode (t x))

def FormulaEffective {n : Nat} (phi : alpha → Formula n) : Prop :=
  Primrec (fun x => GorbowFormulaPrefixCode.encode (phi x))

def HasCertificates (axCheck : alpha → List Nat → Bool) {n : Nat}
    (phi : alpha → Formula n) : Prop :=
  ∃ produce : alpha → Nat, Primrec produce ∧ ∀ x,
    GorbowTheoryNumericCertificate.check (axCheck x) n (formulaCode (phi x)) (produce x) = true

namespace TermEffective

theorem comp {beta : Type} [Primcodable beta] {n : Nat} {t : alpha → Term n}
    (ht : TermEffective t) {g : beta → alpha} (hg : Primrec g) :
    TermEffective (fun x => t (g x)) :=
  Primrec.comp (f := fun x : alpha => GorbowTermPrefixCode.encode (t x)) (g := g) ht hg

theorem constant {n : Nat} (t : Term n) : TermEffective (fun _ : alpha => t) :=
  Primrec.const _

theorem numeral {n : Nat} {f : alpha → Nat} (hf : Primrec f) :
    TermEffective (fun x => (Term.numeral (f x) : Term n)) := by
  have h := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1.comp hf
  exact h.of_eq (fun x => (GorbowCodeConstructorsProof.numeralCalibration n (f x)).symm)

theorem substitution {m n : Nat} {t : alpha → Term m}
    {sigma : alpha → Fin m → Term n} (ht : TermEffective t)
    (hs : ∀ i, TermEffective (fun x => sigma x i)) :
    TermEffective (fun x => GorbowSubstitution.substitute (sigma x) (t x)) := by
  have hd : Primrec (fun x => GorbowLiftedDictionary.dictionary (sigma x)) :=
    Primrec.list_ofFn hs
  have hc := GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.1.comp
    ((Primrec.const m).pair ((Primrec.const n).pair (hd.pair ht)))
  have hg := Primrec.option_getD.comp hc (Primrec.const [])
  apply hg.of_eq
  intro x
  have he := (GorbowSubstitutionCodeProof.exactOutput.1 m n _ _ _).mpr
    ⟨sigma x, t x, rfl, rfl, rfl⟩
  rw [he]
  rfl

end TermEffective

namespace FormulaEffective

theorem comp {beta : Type} [Primcodable beta] {n : Nat} {phi : alpha → Formula n}
    (hp : FormulaEffective phi) {g : beta → alpha} (hg : Primrec g) :
    FormulaEffective (fun x => phi (g x)) :=
  Primrec.comp (f := fun x : alpha => GorbowFormulaPrefixCode.encode (phi x)) (g := g) hp hg

theorem constant {n : Nat} (phi : Formula n) : FormulaEffective (fun _ : alpha => phi) :=
  Primrec.const _

theorem equal {n : Nat} {t u : alpha → Term n}
    (ht : TermEffective t) (hu : TermEffective u) :
    FormulaEffective (fun x => Formula.equal (t x) (u x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
    ((Primrec.const 0).pair (ht.pair hu))

theorem imp {n : Nat} {a b : alpha → Formula n}
    (ha : FormulaEffective a) (hb : FormulaEffective b) :
    FormulaEffective (fun x => Formula.imp (a x) (b x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
    ((Primrec.const 7).pair (ha.pair hb))

theorem all {n : Nat} {a : alpha → Formula (n+1)} (ha : FormulaEffective a) :
    FormulaEffective (fun x => Formula.all (a x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const 10).pair ha)

theorem substitution {m n : Nat} {phi : alpha → Formula m}
    {sigma : alpha → Fin m → Term n} (hp : FormulaEffective phi)
    (hs : ∀ i, TermEffective (fun x => sigma x i)) :
    FormulaEffective (fun x => substituteFormula (sigma x) (phi x)) := by
  have hd : Primrec (fun x => GorbowLiftedDictionary.dictionary (sigma x)) :=
    Primrec.list_ofFn hs
  have hc := GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const m).pair ((Primrec.const n).pair (hd.pair hp)))
  have hg := Primrec.option_getD.comp hc (Primrec.const [])
  apply hg.of_eq
  intro x
  have he := (GorbowSubstitutionCodeProof.exactOutput.2 m n _ _ _).mpr
    ⟨sigma x, phi x, rfl, rfl, rfl⟩
  rw [he]
  rfl

theorem sortedCode {n : Nat} {phi : alpha → Formula n} (hp : FormulaEffective phi) :
    Primrec (fun x => formulaCode (phi x)) :=
  GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp hp

end FormulaEffective

/-- Exact original proofLines, with no existential choice of a different code. -/
theorem compiledCertificate (axCheck : List Nat → Bool) {n : Nat} {phi : Formula n}
    (d : Derivation (GorbowTheoryChecker.ProgramTheory axCheck) phi) :
    GorbowTheoryNumericCertificate.check axCheck n (formulaCode phi)
      (GorbowNumericCertificate.certificateNumber (GorbowTheoryChecker.proofLines axCheck d)) = true := by
  change GorbowTheoryNumericCertificate.check axCheck n
    (formulaRawNumber (GorbowFormulaPrefixCode.encode phi)) _ = true
  rw [GorbowTheoryNumericCertificateProof.calibration]
  have hr := GorbowTheoryCheckerProof.compilationCorrectness axCheck n phi d []
  have hs := (GorbowTheoryCheckerProof.compilationShape axCheck n phi d).2
  simp only [List.append_nil] at hr
  unfold GorbowTheoryChecker.verifies GorbowTheoryChecker.checkProof
  rw [hr]
  cases he : GorbowProofChecker.lineConclusions (GorbowTheoryChecker.proofLines axCheck d) with
  | nil => simp [he] at hs
  | cons head tail =>
      have hh : head = (n, GorbowFormulaPrefixCode.encode phi) := by simpa [he] using hs
      simp [hh]

namespace HasCertificates

theorem comp (axCheck : alpha → List Nat → Bool) {beta : Type} [Primcodable beta]
    {n : Nat} {phi : alpha → Formula n} (hc : HasCertificates axCheck phi)
    {g : beta → alpha} (hg : Primrec g) : HasCertificates (fun x => axCheck (g x)) (fun x => phi (g x)) := by
  obtain ⟨c, hpc, hvc⟩ := hc
  exact ⟨fun x => c (g x), hpc.comp hg, fun x => hvc (g x)⟩

theorem constant (axCheck : List Nat → Bool) {n : Nat} (phi : Formula n)
    (h : Nonempty (Derivation (GorbowTheoryChecker.ProgramTheory axCheck) phi)) :
    HasCertificates (fun _ : alpha => axCheck) (fun _ : alpha => phi) := by
  obtain ⟨d⟩ := h
  refine ⟨fun _ => GorbowNumericCertificate.certificateNumber
      (GorbowTheoryChecker.proofLines axCheck d), Primrec.const _, ?_⟩
  intro x
  exact compiledCertificate axCheck d

theorem mp (axCheck : alpha → List Nat → Bool) {n : Nat} {a b : alpha → Formula n}
    (hb : FormulaEffective b) (hi : HasCertificates axCheck (fun x => Formula.imp (a x) (b x)))
    (ha : HasCertificates axCheck a) : HasCertificates axCheck b := by
  obtain ⟨ci, hci, hvi⟩ := hi
  obtain ⟨ca, hca, hva⟩ := ha
  refine ⟨fun x => mpCertificate n (formulaCode (b x)) (ci x) (ca x), ?_, ?_⟩
  · exact GorbowTheoryCertificateOperationsProof.effectiveModusPonens.comp
      ((Primrec.const n).pair (hb.sortedCode.pair (hci.pair hca)))
  · intro x
    exact GorbowTheoryCertificateOperationsProof.numericModusPonens (axCheck x) n
      (a x) (b x) (ci x) (ca x) (hvi x) (hva x)

theorem generalize (axCheck : alpha → List Nat → Bool) {n : Nat} {a : alpha → Formula (n+1)}
    (ha : FormulaEffective a) (hc : HasCertificates axCheck a) :
    HasCertificates axCheck (fun x => Formula.all (a x)) := by
  obtain ⟨c, hpc, hvc⟩ := hc
  refine ⟨fun x => generalizeCertificate n (formulaCode (.all (a x))) (c x), ?_, ?_⟩
  · exact GorbowTheoryCertificateOperationsProof.effectiveGeneralization.comp
      ((Primrec.const n).pair (ha.all.sortedCode.pair hpc))
  · intro x
    exact GorbowTheoryCertificateOperationsProof.numericGeneralization (axCheck x) n (a x) (c x) (hvc x)

/-- The actual annotation compiler computes the conclusion; the singleton
logicalLine stays in the original List Line certificate format. -/
theorem logical (axCheck : alpha → List Nat → Bool) {n : Nat} (w : alpha → LogicalInstance n)
    (hw : Primrec (fun x => GorbowLogicalAxiomCode.encode (w x))) :
    HasCertificates axCheck (fun x => logicalFormula (w x)) := by
  have hcompile := GorbowLogicalAxiomCodeProof.uniformPrograms.2.2.comp
    ((Primrec.const n).pair hw)
  have hraw : Primrec (fun x => GorbowFormulaPrefixCode.encode (logicalFormula (w x))) := by
    have hg := Primrec.option_getD.comp hcompile (Primrec.const [])
    apply hg.of_eq
    intro x
    have he := (GorbowLogicalAxiomCodeProof.exactCompilation n _ _).mpr ⟨w x, rfl, rfl⟩
    rw [he]
    rfl
  have hline : Primrec (fun x => GorbowProofChecker.logicalLine (w x)) :=
    (Primrec.const n).pair (hraw.pair ((Primrec.const 0).pair
      ((Primrec.fst.comp hw).pair ((Primrec.snd.comp hw).pair
        ((Primrec.const 0).pair (Primrec.const 0))))))
  have hlist := Primrec.list_cons.comp hline (Primrec.const [])
  refine ⟨fun x => GorbowNumericCertificate.certificateNumber
      [GorbowProofChecker.logicalLine (w x)], Primrec.encode.comp hlist, ?_⟩
  intro x
  exact compiledCertificate (axCheck x) (.logical (w x))

end HasCertificates
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family

namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Proof
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations

theorem exactRegistryAxioms : Targets.ExactRegistryAxioms := by
  intro n p sigma
  change decide (GorbowFormulaPrefixCode.encode sigma ∈
    (axioms p).map GorbowFormulaPrefixCode.encode) = true ↔ sigma ∈ axioms p
  rw [decide_eq_true_eq]
  exact List.mem_map_of_injective (GorbowFormulaPrefixCodeProof.encodingInjective 0)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Proof
