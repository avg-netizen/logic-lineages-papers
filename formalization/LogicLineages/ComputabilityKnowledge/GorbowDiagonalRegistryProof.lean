module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplicationProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
open GorbowSyntax GorbowRegistryTuple GorbowRegistryDecoder GorbowSortedSyntaxCode GorbowDiagonalRegistry

private theorem decodeHeaderAt (arity tag : Nat) (args : List Nat) :
    decodeHeader (header arity tag args)=some (arity,tag,args) :=
  (GorbowRegistryDecoderProof.headerExact _ arity tag args).mpr rfl

theorem newDispatch : Comparators.GorbowDiagonalRegistry.NewDispatch := by
  intro code
  simp [functionProgram,decodeHeaderAt]

theorem fallback : Comparators.GorbowDiagonalRegistry.Fallback := by
  constructor
  · intro code h; simp [functionProgram,h]
  · intro arity tag args h; simp [functionProgram,decodeHeaderAt,h]

theorem originalDispatch : Comparators.GorbowDiagonalRegistry.OriginalDispatch := by
  constructor
  · exact GorbowAtomicRegistryProof.originalDispatch.1
  · intro a b c
    have h0 := fallback.2 1 0 [a] (by simp)
    have h1 := fallback.2 2 0 [a,b] (by simp)
    have h2 := fallback.2 2 1 [a,b] (by simp)
    have h3 := fallback.2 2 2 [a,b] (by simp)
    have h4 := fallback.2 2 3 [a,b] (by simp)
    have h5 := fallback.2 2 4 [a,b] (by simp)
    have h6 := fallback.2 3 0 [a,b,c] (by simp)
    simpa only [ground,GorbowAtomicRegistry.ground,h0,h1,h2,h3,h4,h5,h6] using
      GorbowAtomicRegistryProof.originalDispatch.2 a b c

theorem atomicDispatch : Comparators.GorbowDiagonalRegistry.AtomicDispatch := by
  intro a b c
  rw [fallback.2 1 1 [a] (by simp),fallback.2 3 1 [a,b,c] (by simp)]
  exact GorbowAtomicRegistryProof.newDispatch a b c

theorem actualCalibration : Comparators.GorbowDiagonalRegistry.ActualCalibration := by
  intro φ
  rw [newDispatch,GorbowSortedSelfApplicationProof.calibration]
  rfl

private abbrev Header := Nat × Nat × List Nat
private theorem pr_body : Primrec (fun p : Nat × Header =>
    if p.2.1=1 ∧ p.2.2.1=2 ∧ p.2.2.2.length=1 then
      (GorbowSortedSelfApplication.selfApply (p.2.2.2.getD 0 0)).getD 0
    else GorbowAtomicRegistry.functionProgram p.1) := by
  have hs : PrimrecPred (fun p : Nat × Header => p.2.1=1 ∧ p.2.2.1=2 ∧ p.2.2.2.length=1) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).and
      ((Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 2)).and
        (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const 1)))
  have ha : Primrec (fun p : Nat × Header => p.2.2.2.getD 0 0) :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)
  exact Primrec.ite hs
    (Primrec.option_getD.comp (GorbowSortedSelfApplicationProof.uniformPrograms.2.comp ha) (Primrec.const 0))
    (GorbowAtomicRegistryProof.uniformPrograms.2.comp Primrec.fst)

theorem uniformProgram : Comparators.GorbowDiagonalRegistry.UniformProgram := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
    GorbowAtomicRegistryProof.uniformPrograms.2 pr_body.to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [functionProgram,hd])

theorem gorbowDiagonalRegistry : Comparators.GorbowDiagonalRegistry.Target :=
  ⟨newDispatch,originalDispatch,atomicDispatch,actualCalibration,fallback,uniformProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
