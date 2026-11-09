module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerStageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.Proof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB List.Vector

/-- The occurrence tag is input data, so this Program6 can be installed
before the verifier's eventual actual source tag is chosen. -/
theorem programProducer (q : Program 5) : ∃ pG : Program 6, ProducerFor q pG := by
  obtain ⟨produce,hPR,hgood⟩ := EffectiveNumeral.Proof.tagParametricCertificates 5 q
  have hi : Primrec (fun v : List.Vector Nat 6 => produce (v.head,v.tail)) :=
    hPR.comp (Primrec.vector_head.pair Primrec.vector_tail)
  obtain ⟨pG,hG⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 6 _ hi
  refine ⟨pG,?_⟩
  intro n p tag ht inputs
  rw [hG (tag ::ᵥ inputs)]
  simpa only [List.Vector.head_cons,List.Vector.tail_cons] using hgood n p tag ht inputs

theorem sameRegistryProducer : Targets.SameRegistryProducer := by
  obtain ⟨q,hq⟩ := GorbowEnumeratedProvability.Proof.fixedUniversalProgram
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstallCK,hFixed,hInstallG⟩ :=
    RegistryProof.actualRegistry q hq pCK hCK pG
  obtain ⟨fuel,hStage,hGenerated⟩ := StageProof.generatedAtOneStage pF pR q c pG hA hG
  exact ⟨pF,pR,q,c,tagCK,pCK,tagG,pG,hA,hSyntax,hCK,hInstallCK,hFixed,hG,hInstallG,
    fuel,hStage,hGenerated⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.Proof
