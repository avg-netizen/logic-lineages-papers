module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.PackedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LogicProof
theorem exactTick : Targets.InternalTickErasure := by
 intro n p etag ntag otag he hn ho ctx packed raw
 obtain ⟨ptag,ctag,stag,emitTag,atag,htag,ttag,ltag,rtag,hp,hc,hs,hm,ha,hh,ht,hl,hr⟩ := InstallationProof.auxiliaries p etag ntag he hn
 obtain ⟨hrec⟩ := AtomsProof.reconstruct p ptag ltag rtag hp hl hr packed
 obtain ⟨hpacked⟩ := PackedProof.arbitraryTokens p etag ntag otag ptag ctag stag emitTag atag htag ttag
  he hn ho hp hc hs hm ha hh ht (call ltag (packed ::ᵥ nil))
  (call ltag (call rtag (packed ::ᵥ nil) ::ᵥ nil)) (call rtag (call rtag (packed ::ᵥ nil) ::ᵥ nil)) raw
 exact ⟨.mp (.mp (transport etag ntag otag _ packed raw) hrec) hpacked⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickProof
