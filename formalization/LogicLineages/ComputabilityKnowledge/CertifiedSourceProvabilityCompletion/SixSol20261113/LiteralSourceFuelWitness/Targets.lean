module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- Both exact clauses hold in the same original S and at its actual verifier
and core addresses. No new program choice or source rebuild occurs here. -/
def WitnessPackage (l a : Program 1) (x : Program 3) (pF pR : Program 1) : Prop :=
 let q := LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a x bound initial finalizer
 let vtag := GorbowNamedInternalProvability.checkerTag pF
 let qtag := LiteralSourceCoreMP.coreTag pF l a x
 Nonempty (Derivation (S pF pR q) (extractionClause vtag qtag)) ∧
 Nonempty (Derivation (S pF pR q) (injectionClause vtag qtag))

/-- Literal prior three packages at identical witnesses, strengthened by the
two witness clauses only. This is not a monotone-axiom rebuild, not outer MP,
and not source HB2/HB3. No pending numbered statement is marked completed. -/
def SameSourceFuelWitness : Prop :=
 ∃ (l a : Program 1) (x : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag : Nat),
 LiteralValidatedSource.Retained l a x offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a x offset pF pR mtag ∧
 WitnessPackage l a x pF pR
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Targets
