```lean
def oneTwoThree : Array Nat := #[1, 2, 3]

#eval
  match oneTwoThree with
  | #[x, y, z] => some ((x + z) / y)
  | _ => none
```
```lean
def ten : Array Nat :=
  .range 10
```
```lean (name := subarr1)
#eval ten[5:]
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```
```lean (name := subarr2)
#eval ten[2:6]
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```
```lean (name := subarr3)
#eval ten[2:6].array == ten
```
```leanOutput subarr3
true
```
```leanOutput subarr3
true
``````lean -show
variable {w n : Nat}
```
```lean
example : BitVec 8 := 0xff
example : BitVec 8 := 255
example : BitVec 8 := 0b1111_1111
```
```lean -show
-- Inline test
example : (0xff : BitVec 8) = 255 := by rfl
example : (0b1111_1111 : BitVec 8) = 255 := by rfl
```
```leanTerm
5#8
```
```leanOutput spc1
<example>:1:2-1:3: expected end of input
```
```leanOutput spc1
<example>:1:2-1:3: expected end of input
```
```leanOutput spc2
<example>:1:3-1:4: expected no space before
```
```leanOutput spc2
<example>:1:3-1:4: expected no space before
```
```leanOutput spc3
<example>:1:7-1:8: expected end of input
```
```leanOutput spc3
<example>:1:7-1:8: expected end of input
```
```leanTerm
5#(4 + 4)
```
```lean (name := overflow)
#eval 7#2
```
```leanOutput overflow
3#2
```
```leanOutput overflow
3#2
```
```lean
open BitVec
```
```lean
example : BitVec 8 := 1#'(by decide)
```
```lean +error (name := oob)
example : BitVec 8 := 256#'(by decide)
```
```leanOutput oob
Tactic `decide` proved that the proposition
  256 < 2 ^ 8
is false
```
```leanOutput oob
Tactic `decide` proved that the proposition
  256 < 2 ^ 8
is false
```
```lean
def popcount_spec (x : BitVec 32) : BitVec 32 :=
  (32 : Nat).fold (init := 0) fun i _ pop =>
    pop + ((x >>> i) &&& 1)
```
```lean
def popcount (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x &&& 0x0000003F
  x
```
```lean
theorem popcount_correct : popcount = popcount_spec := by
  funext x
  simp [popcount, popcount_spec]
  bv_decide
``````lean (name := e)
#eval 'e'.toString
```
```leanOutput e
"e"
```
```leanOutput e
"e"
```
```lean (name := e')
#eval '\x65'.toString
```
```leanOutput e'
"e"
```
```leanOutput e'
"e"
```
```lean (name := n')
#eval '"'.toString
```
```leanOutput n'
"\""
```
```leanOutput n'
"\""
```
```lean (name := eq)
#eval 'e'.quote
```
```leanOutput eq
"'e'"
```
```leanOutput eq
"'e'"
```
```lean (name := eq')
#eval '\x65'.quote
```
```leanOutput eq'
"'e'"
```
```leanOutput eq'
"'e'"
```
```lean (name := nq')
#eval '"'.quote
```
```leanOutput nq'
"'\\\"'"
```
```leanOutput nq'
"'\\\"'"
``````lean
def f (n : Nat) : Except ε Nat := pure n
```
```lean
def g (n : Nat) : Nat :=
  match f (ε := Empty) n with
  | .error e =>
    Empty.elim e
  | .ok v => v
``````lean -show
section
variable (n : Nat)
```
```lean (name := oneFinCoe)
#eval let one : Fin 3 := ⟨1, by omega⟩; (one : Nat)
```
```leanOutput oneFinCoe
1
```
```leanOutput oneFinCoe
1
```
```lean
example : Fin 5 := 3
example : Fin 20 := 19
```
```lean (name := fivethree)
#eval (5 : Fin 3)
```
```leanOutput fivethree
2
```
```leanOutput fivethree
2
```
```lean (name := fourthree)
#eval ([0, 1, 2, 3, 4, 5, 6] : List (Fin 3))
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```
```lean +error (name := fin0)
example : Fin 0 := 0
```
```leanOutput fin0
failed to synthesize
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput fin0
failed to synthesize
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean +error (name := finK)
example (k : Nat) : Fin k := 0
```
```leanOutput finK
failed to synthesize
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput finK
failed to synthesize
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
``````lean
example : (0.0 : Float) = (0.0 : Float) := by rfl
```
```lean +error (name := zeroPlusZero)
example : (0.0 : Float) = (0.0 + 0.0 : Float) := by rfl
```
```leanOutput zeroPlusZero
Tactic `rfl` failed: The left-hand side
  0.0
is not definitionally equal to the right-hand side
  0.0 + 0.0

⊢ 0.0 = 0.0 + 0.0
```
```leanOutput zeroPlusZero
Tactic `rfl` failed: The left-hand side
  0.0
is not definitionally equal to the right-hand side
  0.0 + 0.0

⊢ 0.0 = 0.0 + 0.0
```
```lean +error (name := zeroPlusZero') -keep
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true :=
  by rfl
```
```leanOutput zeroPlusZero'
Tactic `rfl` failed: The left-hand side
  0.0 == 0.0 + 0.0
is not definitionally equal to the right-hand side
  true

⊢ (0.0 == 0.0 + 0.0) = true
```
```leanOutput zeroPlusZero'
Tactic `rfl` failed: The left-hand side
  0.0 == 0.0 + 0.0
is not definitionally equal to the right-hand side
  true

⊢ (0.0 == 0.0 + 0.0) = true
```
```lean
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true := by
  native_decide
```
```lean (name := ofRed)
#print axioms Float.zero_eq_zero_plus_zero
```
```leanOutput ofRed
'Float.zero_eq_zero_plus_zero' depends on axioms: [Classical.choice, Lean.ofReduceBool, Lean.trustCompiler]
```
```leanOutput ofRed
'Float.zero_eq_zero_plus_zero' depends on axioms: [Classical.choice, Lean.ofReduceBool, Lean.trustCompiler]
```
```lean
#eval ((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0)
```
```lean (name := divZeroPosNeg)
def neg0 : Float := -0.0

def pos0 : Float := 0.0

#eval (neg0 == pos0, 1.0 / neg0 == 1.0 / pos0)
```
```leanOutput divZeroPosNeg
(true, false)
```
```leanOutput divZeroPosNeg
(true, false)
```
```leanTerm
(-2.523 : Float)
```
```leanTerm
(Neg.neg (OfScientific.ofScientific 22523 true 4) : Float)
```
```leanTerm
(413.52 : Float32)
```
```leanTerm
(OfScientific.ofScientific 41352 true 2 : Float32)
```
```lean -show
example : (-2.2523 : Float) = (Neg.neg (OfScientific.ofScientific 22523 true 4) : Float) := by simp [OfScientific.ofScientific]
example : (413.52 : Float32) = (OfScientific.ofScientific 41352 true 2 : Float32) := by simp [OfScientific.ofScientific]
``````lean -show
section
variable (n : Nat)
```
```lean -show
open Int
```
```lean -show
end
```
```lean (name := div0)
#eval Int.ediv 5 0
#eval Int.ediv 0 0
#eval Int.ediv (-5) 0
#eval Int.bdiv 5 0
#eval Int.bdiv 0 0
#eval Int.bdiv (-5) 0
#eval Int.fdiv 5 0
#eval Int.fdiv 0 0
#eval Int.fdiv (-5) 0
#eval Int.tdiv 5 0
#eval Int.tdiv 0 0
#eval Int.tdiv (-5) 0
```
```leanOutput div0
0
```
```leanOutput div0
0
```
```lean -show
example (i j : Int) : Decidable (i ≤ j) := inferInstance
example (i j : Int) : Decidable (i < j) := inferInstance
example (i j : Int) : Decidable (i = j) := inferInstance
``````lean
example : List Nat := [1, 2, 3]
example : List Nat := 1 :: [2, 3]
example : List Nat := 1 :: 2 :: [3]
example : List Nat := 1 :: 2 :: 3 :: []
example : List Nat := 1 :: 2 :: 3 :: .nil
example : List Nat := 1 :: 2 :: .cons 3 .nil
example : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
```
```lean
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split' : List α → List α × List α
  | .nil => (.nil, .nil)
  | x :: [] => (.singleton x, .nil)
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split'' : List α → List α × List α
  | .nil => (.nil, .nil)
  | .cons x .nil=> (.singleton x, .nil)
  | .cons x (.cons x' xs) =>
    let (ys, zs) := split xs
    (.cons x ys, .cons x' zs)
```
```lean -show
-- Test claim
example : @split = @split' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split', List.singleton]

example : @split = @split'' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split'', List.singleton]
``````lean -show
open Std
```
```lean
open Std
```
```lean +error (name:=badNesting) -keep
structure Maze where
  description : String
  passages : HashMap String Maze
```
```leanOutput badNesting
(kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
```
```leanOutput badNesting
(kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
```
```lean
structure RawMaze where
  description : String
  passages : Std.HashMap.Raw String RawMaze
```
```lean
def RawMaze.base (description : String) : RawMaze where
  description := description
  passages := ∅
```
```lean
def RawMaze.insert (maze : RawMaze)
    (direction : String) (next : RawMaze) : RawMaze :=
  { maze with
    passages := maze.passages.insert direction next
  }
```
```lean
inductive RawMaze.WF : RawMaze → Prop
  | mk {description passages} :
    (∀ (dir : String) v, passages[dir]? = some v → WF v) →
    passages.WF →
    WF { description, passages := passages }
```
```lean
theorem RawMaze.base_wf (description : String) :
    RawMaze.WF (.base description) := by
  constructor
  . intro v h h'
    simp [Std.HashMap.Raw.getElem?_empty] at *
  . exact HashMap.Raw.WF.empty

def RawMaze.insert_wf (maze : RawMaze) :
    WF maze → WF next → WF (maze.insert dir next) := by
  let ⟨desc, passages⟩ := maze
  intro ⟨wfMore, wfPassages⟩ wfNext
  constructor
  . intro dir' v
    rw [HashMap.Raw.getElem?_insert wfPassages]
    split <;> intros <;> simp_all [wfMore dir']
  . simp_all [HashMap.Raw.WF.insert]
```
```lean
structure Maze where
  raw : RawMaze
  wf : raw.WF
```
```lean
def Maze.base (description : String) : Maze where
  raw := .base description
  wf := by apply RawMaze.base_wf

def Maze.insert (maze : Maze)
    (dir : String) (next : Maze) : Maze where
  raw := maze.raw.insert dir next.raw
  wf := RawMaze.insert_wf maze.raw maze.wf next.wf
```
```lean
def Maze.description (maze : Maze) : String :=
  maze.raw.description

def Maze.go? (maze : Maze) (dir : String) : Option Maze :=
  match h : maze.raw.passages[dir]? with
  | none => none
  | some m' =>
    Maze.mk m' <| by
      let ⟨r, wf⟩ := maze
      let ⟨wfAll, _⟩ := wf
      apply wfAll dir
      apply h
```
```lean
open Std
```
```lean
def addAlias (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  aliases.insert key (prior.push value)
```
```lean
def addAlias' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  let aliases := aliases.erase key
  aliases.insert key (prior.push value)
```
```lean
def addAlias'' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  aliases.alter key fun prior? =>
    some ((prior?.getD #[]).push value)
``````lean -show
variable (i : Nat)
```
```lean
example (n : Nat) : n < n + 1 := by
  induction n with
  | zero =>
    show 0 < 1
    decide
  | succ i ih => -- ih : i < i + 1
    show i + 1 < i + 1 + 1
    exact Nat.succ_lt_succ ih
```
```lean
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True
  | 0, _ + 1 | _ + 1, 0 => False
  | n + 1, k + 1 => n = k

theorem noConfusionDiagonal (n : Nat) :
    NoConfusion n n :=
  Nat.rec True.intro (fun _ _ => rfl) n

theorem noConfusion (n k : Nat) (eq : n = k) :
    NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

theorem succ_injective : n + 1 = k + 1 → n = k :=
  noConfusion (n + 1) (k + 1)

theorem succ_not_zero : ¬n + 1 = 0 :=
  noConfusion (n + 1) 0
``````lean -show
variable {α : Type u} (v : α) {β : Type v}
```
```lean -show
open Std (HashMap)
variable {Coll} [BEq α] [Hashable α] (a : α) (b : β) {xs : Coll} [GetElem Coll α β fun _ _ => True] {i : α} {m : HashMap α β}
```
```lean
def postalCodes : Std.HashMap Nat String :=
  .empty |>.insert 12345 "Schenectady"
```
```lean (name := getD)
#eval postalCodes[12346]?.getD "not found"
```
```leanOutput getD
"not found"
```
```leanOutput getD
"not found"
```
```lean (name := m)
#eval
  match postalCodes[12346]? with
  | none => "not found"
  | some city => city
```
```leanOutput m
"not found"
```
```leanOutput m
"not found"
```
```lean (name := iflet)
#eval
  if let some city := postalCodes[12345]? then
    city
  else
    "not found"
```
```leanOutput iflet
"Schenectady"
```
```leanOutput iflet
"Schenectady"
```
```lean -show
section
variable {α : Type u} (line : String)
```
```lean
def getAlpha : IO (Option String) := do
  let line := (← (← IO.getStdin).getLine).trim
  if line.length > 0 && line.all Char.isAlpha then
    return line
  else
    return none
```
```lean -show
end
```
```lean -show
variable {α} [DecidableEq α] [LT α] [Min α] [Max α]
``````lean -show
section
variable {α : Type u} {β : Type v} {γ : Type w} {x : α} {y : β} {z : γ}
```
```lean -show
section
variable {α : Sort u} {β : Sort v} {γ : Type w}
```
```lean -show
end
```
```leanTerm
Σ n k : Nat, Fin (n * k)
```
```leanTerm
Σ n : Nat, Σ k : Nat, Fin (n * k)
```
```leanTerm
(n : Nat) × (k : Nat) × Fin (n * k)
```
```leanTerm
Σ (n k : Nat) (i : Fin (n * k)) , Fin i.val
```
```leanTerm
Σ (n : Nat), Σ (k : Nat), Σ (i : Fin (n * k)) , Fin i.val
```
```leanTerm
(n : Nat) × (k : Nat) × (i : Fin (n * k)) × Fin i.val
```
```leanOutput mixedNesting
<example>:1:5-1:7: unexpected token '('; expected ','
```
```leanOutput mixedNesting
<example>:1:5-1:7: unexpected token '('; expected ','
```
```lean -show
section
variable {α : Type} (x : α)
```
```leanTerm
    Σ (b : Bool), if b then Unit else α
    ```
```lean -show
end
```
```lean
def Sum' (α : Type) (β : Type) : Type :=
  Σ (b : Bool),
    match b with
    | true => α
    | false => β
```
```lean
variable {α β : Type}

@[match_pattern]
def Sum'.inl (x : α) : Sum' α β := ⟨true, x⟩

@[match_pattern]
def Sum'.inr (x : β) : Sum' α β := ⟨false, x⟩

def Sum'.swap : Sum' α β → Sum' β α
  | .inl x => .inr x
  | .inr y => .inl y
``````lean -show
variable {α : Type u} {p : Prop}
```
```lean
def NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.data_eq_of_eq h)

theorem s1_eq_s2 : s1 = s2 := by rfl
```
```lean
abbrev NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.data_eq_of_eq h)

theorem s1_eq_s2 : s1 = s2 := by
  ext
  dsimp only [s1, s2]
```
```lean (name := subtype_coe)
abbrev DivBy3 := { x : Nat // x % 3 = 0 }

def nine : DivBy3 := ⟨9, by rfl⟩

set_option eval.type true in
#eval Nat.succ nine
```
```leanOutput subtype_coe
10 : Nat
```
```leanOutput subtype_coe
10 : Nat
``````lean -show
universe u v
```
```lean -show
section
variable {α : Type u} {β : Type v}
```
```lean -show
end
```
```lean -show
section
variable {α : Sort u} {β : Sort v}
```
```lean -show
end
```
```lean
example : Nat × String := panic! "Cant' find it"
```
```lean +error (name := panic)
example : Nat ⊕ String := panic! "Cant' find it"
```
```leanOutput panic
failed to synthesize
  Inhabited (Nat ⊕ String)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput panic
failed to synthesize
  Inhabited (Nat ⊕ String)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
example : Nat ⊕ String :=
  have : Inhabited (Nat ⊕ String) := Sum.inhabitedLeft
  panic! "Cant' find it"
``````lean -show
variable {α : Type u} {e : α}
```
```lean
inductive LazyList (α : Type u) where
  | nil
  | cons : α → LazyList α → LazyList α
  | delayed : Thunk (LazyList α) → LazyList α
deriving Inhabited
```
```lean
def LazyList.toList : LazyList α → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
  | .delayed xs => xs.get.toList
```
```lean
def LazyList.take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x <| .delayed <| take n xs
  | n + 1, .delayed xs => .delayed <| take (n + 1) xs.get

def LazyList.ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (init := .nil) fun i xs =>
    .delayed <| LazyList.cons (f i) xs

def LazyList.append (xs ys : LazyList α) : LazyList α :=
  .delayed <|
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys
```
```lean
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val
```
```lean
def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")
```
```lean (name := lazy1)
#eval xs.toList
```
```leanOutput lazy1
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy1
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy1
[0, 1, 2]
```
```leanOutput lazy1
[0, 1, 2]
```
```lean (name := lazy2)
#eval xs.append ys |>.toList
```
```leanOutput lazy2
xs: 0
xs: 1
xs: 2
ys: 0
ys: 1
ys: 2
```
```leanOutput lazy2
xs: 0
xs: 1
xs: 2
ys: 0
ys: 1
ys: 2
```
```leanOutput lazy2
[0, 1, 2, 0, 1, 2]
```
```leanOutput lazy2
[0, 1, 2, 0, 1, 2]
```
```lean (name := lazy3)
#eval xs.append xs |>.toList
```
```leanOutput lazy3
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy3
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy3
[0, 1, 2, 0, 1, 2]
```
```leanOutput lazy3
[0, 1, 2, 0, 1, 2]
```
```lean (name := lazy4)
#eval xs.append ys |>.take 4 |>.toList
```
```leanOutput lazy4
xs: 0
xs: 1
xs: 2
ys: 0
```
```leanOutput lazy4
xs: 0
xs: 1
xs: 2
ys: 0
```
```leanOutput lazy4
[0, 1, 2, 0]
```
```leanOutput lazy4
[0, 1, 2, 0]
``````lean
structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool

def Permissions.encode (p : Permissions) : UInt8 :=
  let r := if p.readable then 0x01 else 0
  let w := if p.writable then 0x02 else 0
  let x := if p.executable then 0x04 else 0
  r ||| w ||| x

def Permissions.decode (i : UInt8) : Permissions :=
  ⟨i &&& 0x01 ≠ 0, i &&& 0x02 ≠ 0, i &&& 0x04 ≠ 0⟩
```
```lean -show
-- Check the above
theorem Permissions.decode_encode (p : Permissions) : p = .decode (p.encode) := by
  let ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;>
  simp +decide [decode]
```
```lean
example : (255 : UInt8) = 255 := by rfl
example : (256 : UInt8) = 0   := by rfl
example : (257 : UInt8) = 1   := by rfl

example : (0x7f : Int8) = 127  := by rfl
example : (0x8f : Int8) = -113 := by rfl
example : (0xff : Int8) = -1   := by rfl
```
```lean -show
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let classes := [`ShiftLeft, `ShiftRight, `AndOp, `OrOp, `Xor]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
``````lean
def str1 := "String with \
             a gap"
def str2 := "String with a gap"

example : str1 = str2 := rfl
```
```leanOutput foo
<example>:2:0-3:0: unexpected additional newline in string gap
```
```leanOutput foo
<example>:2:0-3:0: unexpected additional newline in string gap
```
```lean
example :
    s!"1 + 1 = {1 + 1}\n" =
    "1 + 1 = " ++ toString (1 + 1) ++ "\n" :=
  rfl
```
```lean (name := evalStr)
example : r"\t" = "\\t" := rfl
#eval r"Write backslash in a string using '\\\\'"
```
```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```
```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```
```lean
example :
    r#"This is "literally" quoted"# =
    "This is \"literally\" quoted" :=
  rfl
```
```lean
example :
    r##"This is r#"literally"# quoted"## =
    "This is r#\"literally\"# quoted" :=
  rfl
``````lean -show
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let signed := [`ISize, `Int8, `Int16, `Int32, `Int64]
  let unsigned := [`USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let types := signed ++ unsigned
  let classes : List Name := [`Add, `Sub, `Mul, `Div, `Mod]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
  for t in signed do
    elabCommand <| ← `(example : Neg $(mkIdent t) := inferInstance)
``````lean -show
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example : LE $(mkIdent t) := inferInstance)
    elabCommand <| ← `(example : LT $(mkIdent t) := inferInstance)
```
```lean -show
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x < y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x ≤ y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x = y) := inferInstance)
``````lean
example (x y z : Nat) : x + (y + z) = (x + z) + y := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
```
```lean
example :
    (fun (x y z : Nat) =>
      x + (y + z))
    =
    (fun x y z =>
      (z + x) + y)
  := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
``````lean -show
open Lean
```
```lean
syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|
    first
      | $t; rep $t
      | skip)

example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl
```
```lean +error
def IsEmpty (xs : List α) : Prop :=
  ¬ xs ≠ []

example (α : Type u) : IsEmpty (α := α) [] := by trivial
```
```lean
def emptyIsEmpty : IsEmpty (α := α) [] := by simp [IsEmpty]

macro_rules | `(tactic|trivial) => `(tactic|exact emptyIsEmpty)

example (α : Type u) : IsEmpty (α := α) [] := by
  trivial
```
```lean
syntax tactic "<|||>" tactic : tactic
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t1
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t2

example : 2 = 2 := by
  rfl <|||> apply And.intro

example : 2 = 2 := by
  apply And.intro <|||> rfl
``````lean -show
variable {n : Nat}
``````lean (name := countdown)
def countdown : Nat → IO Unit
  | 0 =>
    IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown
```
```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
```
```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
``````lean -show
variable {α : Type u}
```
```lean -show
variable {m : Type → Type v} {α : Type} [MonadLiftT BaseIO m] [Inhabited α]
```