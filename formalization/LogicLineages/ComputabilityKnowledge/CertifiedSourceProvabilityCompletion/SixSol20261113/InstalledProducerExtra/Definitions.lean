module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerRegistryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.EquationsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra
open GorbowPRProgram GorbowPRChildTags
/-- A structural carrier, not a newly selected semantic producer. The genuine
original producer remains a literal argument child, and the extra program
is the literal function child of the other argument. -/
def extraWrapper {r : Nat} (extra : Program r) : Program 6 :=
 .composition extra (fun _ => .projection (0 : Fin 6))
def containerArguments {r : Nat} (pG : Program 6) (extra : Program r) : Fin 2 → Program 6 :=
 Fin.cases pG (Fin.cases (extraWrapper extra) Fin.elim0)
def container {r : Nat} (pG : Program 6) (extra : Program r) : Program 6 :=
 .composition (.projection (0 : Fin 2)) (containerArguments pG extra)
def producerTag {r : Nat} (tag : Nat) (pG : Program 6) (extra : Program r) : Nat :=
 tag + argumentTag (.projection (0 : Fin 2)) (containerArguments pG extra) 0
def extraTag {r : Nat} (tag : Nat) (pG : Program 6) (extra : Program r) : Nat :=
 tag + argumentTag (.projection (0 : Fin 2)) (containerArguments pG extra) 1 + 1
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra
