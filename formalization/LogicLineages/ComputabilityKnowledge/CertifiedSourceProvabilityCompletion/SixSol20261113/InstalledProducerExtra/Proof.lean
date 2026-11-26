module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Proof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPublishedDCB
open SixSol20261112

/-- Only structural installation is requested of the container. Its original
producer child and arbitrary extra child are then extracted in the SAME root. -/
theorem actualRegistryWithExtra : Targets.ActualRegistryWithExtra := by
 intro q hq pCK hCK pG r extra
 obtain ⟨pF,pR,c,tagCK,tagCarrier,hActual,hSyntax,hCKInstall,hFixed,hCarrier⟩ :=
   InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK (container pG extra)
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 have hc : (nodes root)[tagCarrier]? = some ⟨6,container pG extra⟩ := hCarrier
 have hProducer := Fuel.Equations.argumentChild root tagCarrier
   (.projection (0 : Fin 2)) (containerArguments pG extra) hc 0
 have hWrapper := Fuel.Equations.argumentChild root tagCarrier
   (.projection (0 : Fin 2)) (containerArguments pG extra) hc 1
 have hExtra := Fuel.Equations.functionChild root
   (tagCarrier + argumentTag (.projection (0 : Fin 2)) (containerArguments pG extra) 1)
   extra (fun _ => .projection (0 : Fin 6)) hWrapper
 exact ⟨pF,pR,c,tagCK,producerTag tagCarrier pG extra,extraTag tagCarrier pG extra,
   hActual,hSyntax,hCKInstall,hFixed,hProducer,hExtra⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Proof
