module

public import LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowLexicalAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowAdmissionAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowAdmissionAlgorithm (Window)
open NumberedWindowAddressAlgorithm (Address addressView)

/-- Closed over the finite original signature and window by the source calibration. -/
structure Settings where
  window : Window
  types : List Nat
  equivalentHeads : HeadPairs

def admitted (s : Settings) (ctx : List Nat) (ty n : Nat) :=
  NumberedWindowLexicalAlgorithm.typed ctx ty n && (NumberedWindowAdmissionAlgorithm.bits s.window n).1

def edge (s : Settings) (ctx : List Nat) (ty a b : Nat) :=
  (NumberedWindowExchangeAlgorithm.bits s.equivalentHeads a b).1 &&
    admitted s ctx ty a && admitted s ctx ty b

def vertices (s : Settings) (n : Nat) :=
  (NumberedWindowCoverBoundsAlgorithm.cover s.window.2 s.types n).getD []

def least (s : Settings) (ctx : List Nat) (ty n : Nat) : Option Nat :=
  NumberedWindowClassAlgorithm.least (edge s ctx ty) (vertices s n) n

def canonical (s : Settings) (a : Address) : Bool :=
  admitted s a.1 a.2.1 a.2.2 && (least s a.1 a.2.1 a.2.2 == some a.2.2)

def scalar (s : Settings) (n : Nat) := (addressView n).any (canonical s)
end LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
