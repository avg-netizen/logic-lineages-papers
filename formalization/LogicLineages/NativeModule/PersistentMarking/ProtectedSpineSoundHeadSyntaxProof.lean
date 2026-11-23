module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundCallSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundHeadSyntaxProof
open Spine

theorem ordinary (f : Head) (bs consumed outer args : Args) :
    applyAux (substitute outer consumed.length (.head f bs)) args consumed =
      apply (substitute (consumed.append outer) 0 (.head f bs)) args := by
  cases args with
  | nil => exact ProtectedSpineSoundCallSyntaxProof.emptyCombined consumed outer (.head f bs)
  | cons a args =>
    have hB := BoundBlockProof.blockArgs consumed outer 0 bs
    simp only [Nat.zero_add] at hB
    simp only [substitute,apply,applyAux,hB,SubstitutionProof.emptyArgsSubstitution]

theorem marked (f : Head) (σ : Ty) (bs es consumed outer args : Args) :
    applyAux (substitute outer consumed.length (.marked f σ bs es)) args consumed =
      apply (substitute (consumed.append outer) 0 (.marked f σ bs es)) args := by
  cases args with
  | nil => exact ProtectedSpineSoundCallSyntaxProof.emptyCombined consumed outer (.marked f σ bs es)
  | cons a args =>
    have hB := BoundBlockProof.blockArgs consumed outer 0 bs
    have hE := BoundBlockProof.blockArgs consumed outer 0 es
    simp only [Nat.zero_add] at hB hE
    simp only [substitute,apply,applyAux,hB,hE,SubstitutionProof.emptyArgsSubstitution]

end LogicLineages.PersistentMarking.ProtectedSpineSoundHeadSyntaxProof
