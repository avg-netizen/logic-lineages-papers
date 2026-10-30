module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryExtensionCode
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCodeProof
open GorbowSyntax GorbowTheoryChecker GorbowTheoryProof GorbowSortedSyntaxCode GorbowTheoryExtensionCode

theorem exactProgram : Comparators.GorbowTheoryExtensionCode.ExactProgram := by
  intro axCheck r raw
  simp [extendProgram]

theorem actualTheory : Comparators.GorbowTheoryExtensionCode.ActualTheory := by
  intro axCheck R σ
  rw [ProgramTheory,exactProgram]
  change (ProgramTheory axCheck σ ∨ GorbowFormulaPrefixCode.encode σ=GorbowFormulaPrefixCode.encode R) ↔ _
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (GorbowFormulaPrefixCodeProof.encodingInjective 0 h)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (congrArg GorbowFormulaPrefixCode.encode h)

private theorem certificateAt (axCheck : List Nat → Bool) (σ : Sentence) :
    (∃ c, GorbowTheoryNumericCertificate.check axCheck 0 (formulaCode σ) c=true) ↔
      Nonempty (Derivation (ProgramTheory axCheck) σ) := by
  rw [GorbowTheoryNumericCertificateProof.proofEquivalence]
  constructor
  · rintro ⟨φ,h,hp⟩
    have he := GorbowSortedSyntaxCodeProof.actualInjection.1 0 h
    subst φ
    exact hp
  · intro h; exact ⟨σ,rfl,h⟩

theorem certificateDeduction : Comparators.GorbowTheoryExtensionCode.CertificateDeduction := by
  intro axCheck R σ
  rw [(GorbowSortedBooleanCodeProof.actualConstructors 0 R σ).2.1]
  rw [certificateAt,certificateAt]
  have he : ProgramTheory (extendProgram axCheck (GorbowFormulaPrefixCode.encode R))=
      GorbowClosedDeduction.extend (ProgramTheory axCheck) R := by
    funext τ
    exact propext (actualTheory axCheck R τ)
  rw [he]
  exact GorbowClosedDeductionProof.closedExtension _ R σ

theorem uniformExtension : Comparators.GorbowTheoryExtensionCode.UniformExtension := by
  intro axCheck ha
  exact Primrec.or.comp (ha.comp Primrec.snd) ((Primrec.eq.comp Primrec.snd Primrec.fst).decide)

theorem gorbowTheoryExtensionCode : Comparators.GorbowTheoryExtensionCode.Target :=
  ⟨exactProgram,actualTheory,certificateDeduction,uniformExtension⟩
end LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCodeProof
