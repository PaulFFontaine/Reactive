import Mathlib.Data.List.Induction
/-! The aim of this (experimental) module is to study Arrowized
Functionnal Reactive Programming library.
Discrete time representation is used.


-/
/-- A value of type `Ty` represents a type that can be used as input or output of an `SF` -/
inductive Ty : Type where
  |int : Ty
  |prod : Ty -> Ty -> Ty
  |arrow : Ty -> Ty -> Ty

def Ty.toType
  |int => Int
  |prod x y => x.toType × y.toType
  |arrow x y => x.toType -> y.toType

theorem Ty.arrow_toType : (toType t1 -> toType t2) = toType (arrow t1 t2) := by
  simp!
/-- Conceptually, an `SF` (Stream Function) with input type i and output type `o`
 maps a function of type `Nat -> i`
to a function of type (`Nat -> o`) such that output at time `n`
depends only of inputs at time smaller than `n`.
 You can also see it as a state machine that reads input of type `i` and write outputs of type `o`
 So an SF is both a specification of a stream function (see `SF.denotationRToL`)
 and a state machine implementing this specification (see `SF.run`)

 The selection of the primitives is intended to be such that any simple stream function as a single
 way of beeing built
-/
inductive SF : Ty -> Ty -> Type where
  |I : SF i i
  |KI : SF i (Ty.arrow o o)
  |IU : o.toType -> SF i (Ty.arrow o o) -> SF i o
  |App : SF i (Ty.arrow o1 o2) -> SF i o1 -> SF i o2

abbrev SF.identity {i} : SF i i := I
abbrev SF.constId {i o} : SF i (Ty.arrow o o) := KI
abbrev SF.const {i o} (x : o.toType) : SF i o := IU x KI

abbrev SF.map (f : o1.toType -> o2.toType) : SF i o1 -> SF i o2 := App (const f)

/-- `SF.liftA2` is behaves like a map with a function of arity 2 instead of 1 -/
abbrev SF.liftA2 (f : o1.toType -> o2.toType -> o3.toType) (sf : SF i o1) : SF i o2 -> SF i o3
 := App (sf.map f)

abbrev SF.delay (x : o.toType) (sf : SF i o) : SF i o :=
  IU x (map (@Function.const o.toType o.toType) sf)
/-- `SF.arr` converts a function into a stream function -/
def SF.arr (f : i.toType -> o.toType) : SF i o := App (const f) I
/-- `SF.compo` is the analogous of function composition for stream functions
the important point is that SF composition can be expressed without beeing a primitive/data constructor-/
@[simp]
def SF.compo : SF o1 o2 -> SF i o1 -> SF i o2
  |I, sf => sf
  |KI, sf => KI
  |IU init update, sf => IU init (update.compo sf)
  |App f x, sf => App (f.compo sf) (x.compo sf)

@[simp]
theorem SF.compo_I_right (sf : SF i o) : sf.compo I = sf := by induction sf with
  | I => simp
  | KI => simp
  | IU init update ih => simp[ih]
  | App f x ih1 ih2 => simp[ih1,ih2]

@[simp]
theorem SF.compo_I_left {i o} (sf : SF i o) : I.compo sf = sf := by induction sf with
  | I => simp
  | KI => simp
  | IU init update ih => simp
  | App f x ih1 ih2 => simp


/-- `SF.run input sf` runs the given `sf` as a state machine. Similar to `State.run`
`SF.run`defines an operationnal semantics of `SF`values -/
def SF.run : i.toType -> SF i o  -> o.toType × SF i o
  |input,I => (input,I)
  |_,KI=> (id,KI)
  |input,IU init update => let (result,state) := update.run input
                     let x := result init
                     (x, IU x state)
  |input,App f x=> let (resultF,stateF) := f.run input
              let (resultX,stateX) := x.run input
              (resultF resultX, stateF.App stateX)
/-- `SF.eval input sf` runs the given `sf` and returns the resulting output
discarding the resulting state -/
def SF.eval input (sf : SF i o) := (sf.run input).fst
/-- `SF.exec input sf` runs the given `sf` and returns the resulting state
discarding the resulting output -/
def SF.exec input (sf : SF i o) := (sf.run input).snd


@[simp]
theorem SF.eval_I input : (@I i).eval input = input := by simp[eval,run]
@[simp]
theorem SF.exec_I input : (@I i).exec input = I := by simp[exec,run]
@[simp]
theorem SF.eval_KI input : (@KI i o).eval input = id := by simp only[eval,run];eq_refl
@[simp]
theorem SF.exec_KI input : (@KI i o).exec input = KI := by simp[exec,run]
@[simp]
theorem SF.eval_App input f x : (@App i o1 o2 f x).eval input = (f.eval input) (x.eval input):=
  by simp[eval,run]
@[simp]
theorem SF.exec_App input f x : (@App i o1 o2 f x).exec input = App (f.exec input) (x.exec input):=
  by simp[exec,run]
@[simp]
theorem SF.eval_IU input init update : (@IU i o init update).eval input = update.eval input init :=
 by simp[eval,run]
@[simp]
theorem SF.exec_IU input init update : (@IU i o init update).exec input =
 IU (update.eval input init) (update.exec input) := by simp[exec,run,eval]
@[simp]
theorem SF.eval_compo input ( sf1 : SF o1 o2) (sf2 : SF i o1) : (sf1.compo sf2).eval input
 = sf1.eval (sf2.eval input) := by induction sf1 with
   | I => simp
   | KI => simp only [compo, eval_KI]; eq_refl
   | IU init update ih => simp[ih]
   | App sf1 sf2 ih1 ih2 => simp[ih1,ih2]
@[simp <-]
theorem SF.exec_compo input (sf1 : SF o1 o2) (sf2 : SF i o1) : (sf1.compo sf2).exec input
 = (sf1.exec (sf2.eval input)).compo (sf2.exec input):= by induction sf1 with
   | I => simp [eval,compo]
   | KI => simp[eval,compo]
   | IU init update ih => simp[ih,compo]
   | App sf1 sf2 ih1 ih2 => simp[ih1,ih2,compo]


/-- `SF.stateRtoL` computes the resulting state after processing a sequence of input.
The input sequence must be given as a stack, i.e with inputs from the latest to the earliest -/
def SF.stateRtoL (inputStack : List i.toType) (sf : SF i o) := List.foldr exec sf inputStack

@[simp]
theorem SF.stateRtoL_concat input inputStack (sf : SF i o) : sf.stateRtoL (inputStack ++ [input])
 = (sf.exec input).stateRtoL inputStack := by simp[stateRtoL]
@[simp]
theorem SF.stateRtoL_cons input inputStack (sf : SF i o) : sf.stateRtoL (input :: inputStack) =
 (sf.stateRtoL inputStack).exec input := by simp[stateRtoL]

@[simp]
theorem SF.stateRtoL_I inputStack : (@I i).stateRtoL inputStack = I :=
by simp only[stateRtoL]; induction inputStack with
  | nil => eq_refl
  | cons x xs ih => simp[List.foldr, ih]

@[simp]
theorem SF.stateRtoL_KI inputStack : (@KI i o).stateRtoL inputStack = KI :=
by simp only[stateRtoL]; induction inputStack with
  | nil => eq_refl
  | cons x xs ih => simp[List.foldr, ih]

@[simp]
theorem SF.stateRtoL_App inputStack f x : (@App i o1 o2 f x).stateRtoL inputStack =
 App (f.stateRtoL inputStack) (x.stateRtoL inputStack) :=
by simp only[stateRtoL]; induction inputStack with
  | nil => eq_refl
  | cons x xs ih => simp[List.foldr, ih]

@[simp]
theorem SF.stateRtoL_IU_not_nil inputStack {h : inputStack ≠ []} init update :
  (@IU i o init update).stateRtoL inputStack =
  IU (((IU init update).stateRtoL inputStack.tail).eval (inputStack.head h))
     (update.stateRtoL inputStack)
  := by induction inputStack with
    | nil => contradiction
    | cons head tail ih =>  cases tail
                            · eq_refl
                            simp[stateRtoL] at ih
                            simp[stateRtoL,ih]

@[simp]
theorem SF.stateRtoL_nil (sf : SF i o) : sf.stateRtoL [] = sf := by simp[stateRtoL]

/-- `SF.denotationRtoLAux` computes the resulting output after processing
a non-empty sequence of inputs.
The inputs must be given from the earliest to the latest.
The `last` argument is the latest piece of input. -/
@[simp]
def SF.denotationRtoLAux (last : i.toType) (previous : List (i.toType)) : SF i o -> o.toType
  |I => last
  |KI => id
  |App f x => (f.denotationRtoLAux last previous) (x.denotationRtoLAux last previous)
  |IU init update => update.denotationRtoLAux last previous (match previous with
    |[] => init
    |(x::xs) => (IU init update).denotationRtoLAux x xs)
/-- `SF.denotationRtoL` computes the resulting output after processing
a non-empty sequence of inputs.
The inputs must be given from the latest to the earliest -/
def SF.denotationRtoL {i o} (inputStack : List i.toType) (h : inputStack ≠ []) :
 SF i o -> (o.toType) := denotationRtoLAux (inputStack.head h) (inputStack.tail)

theorem SF.denotationRtoL_I {i} inputStack {h} : denotationRtoL inputStack h (@I i) =
 inputStack.head h := by simp[denotationRtoL]
@[simp]
theorem SF.denotationRtoL_KI {i o} inputStack {h} : denotationRtoL inputStack h (@KI i o) = id :=
by simp only [denotationRtoL,denotationRtoLAux]; eq_refl
@[simp]
theorem SF.denotationRtoL_App {i o1 o2} inputStack {h} f x : denotationRtoL inputStack h (@App i o1 o2 f x) =
  (f.denotationRtoL inputStack h) (x.denotationRtoL inputStack h) := by simp[denotationRtoL]

@[simp]
theorem SF.denotationRtoL_IU inputStack {h} init update :
 denotationRtoL inputStack h (@IU i o init update) =
  update.denotationRtoL inputStack h (if h1 : inputStack.tail.isEmpty then init
    else (IU init update).denotationRtoL inputStack.tail (by simp at h1; simp[h1])):=
      by induction inputStack with
        |nil => contradiction
        |cons head tail ih =>  simp[denotationRtoL] at ih; simp[denotationRtoL,ih]; cases tail with
          | nil => simp
          | cons x xs => cases xs <;> simp

/-- `SF.stateLToR` computes the resulting state after processing a non-empty sequence of inputs.
The inputs must be given from the earliest to the latest -/
def SF.stateLToR inputQueue (sf : SF i o) := List.foldl (fun sf => sf.exec) sf inputQueue

theorem SF.stateLToR_eq_stateRtoL inputQueue (sf : SF i o) : sf.stateLToR inputQueue =
 sf.stateRtoL inputQueue.reverse := by simp[stateLToR,stateRtoL]

@[simp]
theorem SF.stateLToR_concat input inputQueue (sf : SF i o) :
sf.stateLToR (inputQueue ++ [input]) = (sf.stateLToR inputQueue).exec input := by simp[stateLToR]
@[simp]
theorem SF.stateLToR_cons input inputQueue (sf : SF i o) : sf.stateLToR (input :: inputQueue) =
 (sf.exec input).stateLToR inputQueue := by simp[stateLToR]

@[simp]
theorem SF.stateLToR_I inputQueue : (@I i).stateLToR inputQueue = I :=
by simp only[stateLToR]; induction inputQueue with
  | nil => eq_refl
  | cons x xs ih => simp[List.foldl, ih]

@[simp]
theorem SF.stateLToR_KI inputQueue : (@KI i o).stateLToR inputQueue = KI :=
by simp only[stateLToR]; induction inputQueue with
  | nil => eq_refl
  | cons x xs ih => simp[List.foldl, ih]

@[simp]
theorem SF.stateLToR_App inputQueue f x : (@App i o1 o2 f x).stateLToR inputQueue =
 App (f.stateLToR inputQueue) (x.stateLToR inputQueue) := by simp[stateLToR_eq_stateRtoL]

@[simp]
theorem SF.stateLToR_IU_not_nil inputQueue {h : inputQueue ≠ []} init update :
  (@IU i o init update).stateLToR inputQueue =
  (IU (update.eval (inputQueue.head h) init) (update.exec (inputQueue.head h))).stateLToR
   (inputQueue.tail)
    := by simp only [stateLToR]; induction inputQueue with
     | nil => contradiction
     | cons  => simp
@[simp]
theorem SF.stateLToR_nil (sf : SF i o) : sf.stateLToR [] = sf := by simp[stateLToR]

theorem SF.run_eq_eval_exec (sf : SF i o) x : sf.run x = (sf.eval x, sf.exec x) := by
  induction sf <;> simp!
  · rename_i ih
    simp[ih]
  rename_i ih1 ih2
  simp[ih1,ih2]


theorem SF.denotationRtoLAux_eq_eval_stateRtoL last previous (sf : SF i o) :
  sf.denotationRtoLAux last previous = (sf.stateRtoL previous).eval last := by
    revert previous last
    induction sf with
      |I => simp
      |KI => simp; grind only
      |App f x ihf ihx =>
        simp[ihf,ihx]
      |IU init update ih =>
       intro last previous
       revert last
       induction previous with
        |nil => simp[ih]
        |cons x xs ih1 =>
          simp[ih,ih1]

theorem SF.stateRtoL_eq_foldr (sf : SF i o) (xs : List i.toType) :
  sf.stateRtoL xs = List.foldr exec sf xs := match xs with
    |[] => by simp
    |(y::ys) => have ih := stateRtoL_eq_foldr sf ys
                match sf with
                  |I => by simp[<-ih]
                  |KI => by simp[<-ih]
                  |App f x => by simp[<-ih]
                  |IU init update => by have ih1 := stateRtoL_eq_foldr update (y::ys)
                                        simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                          stateRtoL_IU_not_nil, List.head_cons, List.tail_cons, ih1,
                                          List.foldr_cons, ← ih]
                                        cases ys
                                        · rfl
                                        rename_i head tail
                                        have ih2 := stateRtoL_eq_foldr update tail
                                        have ih3 := stateRtoL_eq_foldr update (head::tail)
                                        simp![ih2,ih3]
theorem SF.denotationRtoLAux_concat x xs y (sf : SF i o) : sf.denotationRtoLAux x (xs++[y])=
 (sf.exec y).denotationRtoLAux x xs:= by
 revert x xs
 induction sf with
  |I => simp
  |KI =>  simp only [denotationRtoLAux, exec_KI, forall_const]; grind only
  |App f x1 ihf ihx1 =>
    simp[ihf,ihx1]
  |IU init update ih =>
    intro x xs
    revert x
    induction xs with
     |nil =>
      simp[denotationRtoLAux_eq_eval_stateRtoL]
     |cons head tail tail_ih =>
      unfold denotationRtoLAux
      simp only [List.cons_append, exec_IU]
      intro x
      rw[tail_ih,<-List.cons_append,ih]
      apply congr
      · eq_refl
      unfold exec
      rw[run_eq_eval_exec]
      eq_refl




/-- `SF.denotationLToRAux` computes the resulting output after processing
a non-empty sequence of input.
The input sequence must be given as a queue, i.e with inputs from the earliest to the latest.
The `first` argument is the earliest piece of input. -/
def SF.denotationLToRAux (first : i.toType) (next : List (i.toType)) : SF i o -> o.toType
  |I => (first::next).getLast (by simp)
  |KI => id
  |App f x => (f.denotationLToRAux first next) (x.denotationLToRAux first next)
  |IU init update => match next with
    |[] => update.eval first init
    |(x::xs) => ((IU init update).exec first).denotationLToRAux x xs

/-- `SF.denotationLToR` computes the resulting output after processing
a non-empty sequence of inputs.
The input sequence must be given as a queue, i.e with inputs from the earliest to the latest -/
def SF.denotationLToR (inputQueue : List i.toType) (h : inputQueue ≠ []) : SF i o -> (o.toType)
  := denotationLToRAux (inputQueue.head h) (inputQueue.tail)
