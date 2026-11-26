module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113
open SixSol20261112

theorem bundleInstallation : Targets.BundleInstallation := by
 intro xs
 induction xs with
 | nil =>
   intro n p tag htag a ha
   simp at ha
 | cons first rest ih =>
   intro n p tag htag a ha
   let wrapped := InstalledProducerExtra.extraWrapper first.2
   let args := InstalledProducerExtra.containerArguments wrapped (bundle rest)
   have hhead := Fuel.Equations.argumentChild p tag
    (.projection (0 : Fin 2)) args htag 0
   have hfirst := Fuel.Equations.functionChild p
    (InstalledProducerExtra.producerTag tag wrapped (bundle rest))
    first.2 (fun _ => .projection (0 : Fin 6)) hhead
   have htailWrapper := Fuel.Equations.argumentChild p tag
    (.projection (0 : Fin 2)) args htag 1
   have htail := Fuel.Equations.functionChild p
    (tag + argumentTag (.projection (0 : Fin 2)) args 1)
    (bundle rest) (fun _ => .projection (0 : Fin 6)) htailWrapper
   rcases List.mem_cons.mp ha with ha | ha
   · subst a
     exact ⟨InstalledProducerExtra.producerTag tag wrapped (bundle rest) + 1,hfirst⟩
   · exact ih n p (InstalledProducerExtra.extraTag tag wrapped (bundle rest)) htail a ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof.bundleInstallation
