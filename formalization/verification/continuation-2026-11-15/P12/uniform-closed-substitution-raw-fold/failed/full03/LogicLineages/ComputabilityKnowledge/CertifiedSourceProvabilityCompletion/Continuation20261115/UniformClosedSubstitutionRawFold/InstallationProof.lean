module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open SixSol20261112.Fuel
def arguments : Fin 3 → Program 3 :=
 fun i => (applyOne HistoryLengthOffset.lengthProgram (.projection 0) ::ᵥ initial ::ᵥ (.projection 2) ::ᵥ nil).get i
def packedTag (tag : Nat) := tag + argumentTag (HistoryDecoder.decoder true) (fun _ : Fin 1 => finalPacked) 0
def iteratorTag (tag : Nat) := packedTag tag + 1
def lengthTag (tag : Nat) := packedTag tag + argumentTag UniformClosedSubstitutionFold.iterator arguments 0 + 1
theorem installed {n : Nat} (p : Program n) tag
 (hf : (nodes p)[tag]? = some ⟨3,foldCode⟩) :
 (nodes p)[tag+1]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
 (nodes p)[iteratorTag tag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩ ∧
 (nodes p)[lengthTag tag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ := by
 have hd := Equations.functionChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => finalPacked) hf
 have hpacked := Equations.argumentChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => finalPacked) hf 0
 have hi := Equations.functionChild p (packedTag tag) UniformClosedSubstitutionFold.iterator arguments hpacked
 have hlen := Equations.argumentChild p (packedTag tag) UniformClosedSubstitutionFold.iterator arguments hpacked 0
 have hl := Equations.functionChild p _ HistoryLengthOffset.lengthProgram (fun _ : Fin 1 => (.projection (0 : Fin 3))) hlen
 exact ⟨hd,hi,hl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.InstallationProof
