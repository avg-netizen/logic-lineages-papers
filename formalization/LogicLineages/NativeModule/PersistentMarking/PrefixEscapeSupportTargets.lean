module

public import LogicLineages.NativeModule.PersistentMarking.AuxiliaryTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.PrefixEscapeSupportTargets
open Spine

/-- Raw simultaneous bound-block composition, including outer indices. -/
def BlockComposition : Prop := ∀ inner outer d q,
  substitute inner d (substitute outer (d + inner.length) q) = substitute (inner.append outer) d q
def BlockArgsComposition : Prop := ∀ inner outer d qs,
  substituteArgs inner d (substituteArgs outer (d + inner.length) qs) = substituteArgs (inner.append outer) d qs

def ClosedShift : Prop := ∀ q σ, Typed EmptyContext q σ → ∀ k, shift k 0 q = q
def ClosedSubstitute : Prop := ∀ q σ, Typed EmptyContext q σ → ∀ values, substitute values 0 q = q

/-- Retained original extras plus any full ordered list of prefix copies are
refined by the original whole owner at the actual output annotation. -/
def PrefixResult : Prop := ∀ S f ρ τ base extras pref added,
  PaperTerm S (.marked f ρ base extras) ρ → Prefix pref extras → PrefixCopies f base extras added →
  Refines S (.marked f τ base extras) (.marked f τ base (pref.append added))

/-- Two actual auxiliary calls differing by insertion of an older prefix-copy
block. The escape alternative explicitly records the blocked original call. -/
def Splicing : Prop := ∀ S f ρ τ base extras q newer older args w,
  PaperTerm S (.marked f ρ base extras) ρ →
  PrefixCopies f base extras older → PrefixCopies f base extras args →
  w.type = τ →
  applyAux (substitute older newer.length q) args newer = some w →
  applyAux q args (newer.append older) = some w ∨
    (applyAux q args (newer.append older) = none ∧ Refines S (.marked f τ base extras) w)

/-- Genuine staged auxiliary prefix calls, preserving all accumulated values. -/
def AuxiliaryTwoStage : Prop := ∀ S f ρ τ base extras q values first second r w,
  PaperTerm S (.marked f ρ base extras) ρ →
  PrefixCopies f base extras values → PrefixCopies f base extras first → PrefixCopies f base extras second →
  w.type = τ → applyAux q first values = some r → apply r second = some w →
  applyAux q (first.append second) values = some w ∨ Refines S (.marked f τ base extras) w
end LogicLineages.PersistentMarking.PrefixEscapeSupportTargets
