
import Batteries.Data.List.Basic
import Aesop
abbrev NonZero := {n : Nat // n > 0}
abbrev Signal (α : Type u) := Nat -> α

abbrev SigFun (α β : Type u ) := Signal α -> Signal β


abbrev Reactive (α β : Type u ) := List α -> β


def Signal.history (s : Signal α) (n : Nat) : List α :=
  (List.range' 1 (n+1)).map s


def Reactive.history (r : Reactive α β) (input : List α) : List β :=
  input.inits.map r
structure SigFun.reactive {α β} (sf : SigFun α β) where
  val : Reactive α β
  property : ∀s n, n > 0 -> sf s n = val (s.history n)

def SigFun.reactive_comp {sf1 : SigFun β γ} {sf2 : SigFun α β} (h1 : reactive sf1) (h2 : reactive sf2) : reactive (sf1 ∘ sf2)
:= {val := fun input => h1.val (h2.val.history input),
    property := by
      have p1 := h1.property
      have p2 := h2.property
      simp[p1,Signal.history,Reactive.history]
      intro s n h
      induction n
      contradiction
      rw[p1]



}
