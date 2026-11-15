module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.HistoryMachine
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev original (v l a : Program 1) (x : Program 3) : Program 3 := HistoryKernel.kernel v l a x
abbrev extended (test v l a : Program 1) (x : Program 3) : Program 3 := HistoryKernel.kernel v (extend test l) a x
namespace Targets
def InternalActiveStep (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (oldTag newTag ptag ctag : Nat),
 (nodes p)[oldTag]? = some ⟨3,original valid old arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨3,extended test valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (index fuel history line rest output : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (HistoryKernel.kernelCall oldTag
   (HistoryKernel.activeState ptag ctag history line rest) index fuel)
   (HistoryKernel.pairCall ptag (.succ output) rest))
  (.equal (HistoryKernel.kernelCall newTag
   (HistoryKernel.activeState ptag ctag history line rest) index fuel)
   (HistoryKernel.pairCall ptag (.succ output) rest))))
end Targets
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Kernel
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.State
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.HistoryMachine
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawUniversalStateRetention
namespace Targets
def InternalPairedStep (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,Kernel.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,Kernel.extended test valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (option lines index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag (HistoryKernel.pairCall ptag option lines) index fuel output rest))
def InternalStateStep (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,Kernel.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,Kernel.extended test valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (state index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag state index fuel output rest))
end Targets
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.State
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Simulation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.HistoryMachine
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawUniversalSimulation
namespace Targets
def InternalKernelSimulation (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,Kernel.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,Kernel.extended test valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (state newState index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (relation ptag state newState)
 (relation ptag (HistoryKernel.kernelCall ot state index fuel)
                (HistoryKernel.kernelCall nt newState index fuel))))
end Targets
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Simulation
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Iteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.HistoryMachine
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev original (v l a : Program 1) (x : Program 3) : Program 4 := iterator (HistoryKernel.kernel v l a x)
abbrev extended (test v l a : Program 1) (x : Program 3) : Program 4 := iterator (HistoryKernel.kernel v (extend test l) a x)
namespace Targets
def InternalIteratorRetention (test : Program 1) : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨4,original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨4,extended test valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (count state index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (iterationCall ot count state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))
       (.equal (iterationCall nt count state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))))
end Targets
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Iteration
