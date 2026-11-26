module
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbe
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitter
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFreeAddress (freshName)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal chooseBranch)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

abbrev Fields := Nat × Nat × Nat

/-- Same raw probe guards, address, arrow domain and fresh literal bound.
The first successful coordinate is the original ordered sparse field
code, not Encodable.encode of the decoded list. -/
def probeFields (s : Settings) (q : Nat) : Option Fields :=
  if scalar s q then do
    let a ← addressView q
    let (domain,_) ← arrowView a.2.1
    return (pack a.1,domain,freshName a.2.2)
  else none

def goodSpec (s : Settings) (q : Nat) : Nat := (probeFields s q).isSome.toNat
def contextSpec (s : Settings) (q : Nat) : Nat := ((probeFields s q).map Prod.fst).getD 0
def typeSpec (s : Settings) (q : Nat) : Nat := ((probeFields s q).map (fun r => r.2.1)).getD 0
def nameSpec (s : Settings) (q : Nat) : Nat := ((probeFields s q).map (fun r => r.2.2)).getD 0

/-- Four actual program leaves, with no assumptions or theorem fields.
The independent indicator distinguishes none from legitimate zero
context or type coordinates. -/
structure Selectors where
  good : Program 1
  context : Program 1
  domain : Program 1
  name : Program 1

def calibrated (s : Settings) (p : Selectors) : Prop :=
  (∀ q, evaluate p.good (q ::ᵥ nil) = goodSpec s q) ∧
  (∀ q, evaluate p.context (q ::ᵥ nil) = contextSpec s q) ∧
  (∀ q, evaluate p.domain (q ::ᵥ nil) = typeSpec s q) ∧
  (∀ q, evaluate p.name (q ::ᵥ nil) = nameSpec s q)

def packedFree (packedContext domain name : Nat) : Nat :=
  packNode 3 [packedContext,domain,packNode 0 [domain,name]]

def consOf {n : Nat} (head tail : Program n) : Program n :=
  .composition fieldCons (Fin.cons head (Fin.cons tail Fin.elim0))

/-- Exactly seven literal original sparse field conses, with the same
packed context and type at their original coordinates. -/
def packedEmitter : Program 3 :=
  let ctx : Program 3 := .projection 0
  let t : Program 3 := .projection 1
  let n : Program 3 := .projection 2
  let z := zeroAt 3
  let variablePayload := consOf z (consOf t (consOf n z))
  consOf (literal 3 3) (consOf ctx (consOf t (consOf variablePayload z)))

def emitSelected (p : Selectors) : Program 1 :=
  .composition packedEmitter (Fin.cons p.context (Fin.cons p.domain (Fin.cons p.name Fin.elim0)))

def chooseFresh (p : Selectors) : Program 1 :=
  chooseBranch p.good (zeroAt 1) (.composition .succ (Fin.cons (emitSelected p) Fin.elim0))

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitter
